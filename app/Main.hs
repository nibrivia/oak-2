{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Use tuple-section" #-}
module Main (main) where

import Control.Monad (foldM_)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Function
import qualified Data.Map as Map
import Debug.Trace
import Parser
import System.IO
import qualified Text.Parsec as Parsec

data ErrorType = ParseError | RuntimeError deriving (Eq, Show)

data Error = Error
  { errorType :: ErrorType,
    message :: String,
    stack :: [String]
  }
  deriving (Eq)

instance Show Error where
  show (Error eType msg sTrace) =
    (sTrace & map ("  " ++) & reverse & unlines) ++ "  \x1b[1;31m" ++ show eType ++ ":\x1b[0m\x1b[1m " ++ msg ++ "\x1b[0m"

debugPipe :: (Show b) => String -> b -> b
debugPipe name x = trace (name ++ ": " ++ show x) x

makeChildEnv :: Env -> Env
makeChildEnv parentEnv = Env Map.empty (Just parentEnv)

-- TODO make sure failures during executing in a different env does not screw return env
type Computation a = (ExceptT Error (ReaderT [String] (State Env))) a

-- | Error monad base operations
compute :: Env -> Computation a -> (Either Error a, Env)
-- compute env comp = runState (runReaderT (runExceptT comp) []) env
compute env comp =
  comp
    & runExceptT
    & flip runReaderT []
    & flip runState env

getEnv :: Computation Env
getEnv = lift (lift get)

setEnv :: Env -> Computation ()
setEnv = lift . lift . put

withTrace :: String -> Computation a -> Computation a
withTrace str comp = do
  cur_stack <- curStack
  mapExceptT (local (const (str : cur_stack))) comp

curStack :: Computation [String]
curStack = lift ask

throwWithTrace :: ErrorType -> String -> Computation a
throwWithTrace errType msg = do
  cur_stack <- curStack
  let new_err = Error {errorType = errType, message = msg, stack = cur_stack}
  throwE new_err

runInEnv :: Env -> Computation a -> Computation a
runInEnv env comp = do
  cur_env <- getEnv
  setEnv env
  finallyE comp (setEnv cur_env) -- we must always got back to our initial env

emptyEnv :: Env
emptyEnv = Env Map.empty Nothing

runInChildEnv :: Computation a -> Computation a
runInChildEnv comp = do
  env <- getEnv
  let childEnv = makeChildEnv env
  runInEnv childEnv comp

bindFromOtherEnv :: String -> Expression -> Env -> Computation ()
bindFromOtherEnv name expression exprEnv =
  -- ADD LAZINESS
  withTrace ("bindFromOtherEnv " ++ name ++ " = " ++ show expression) $ do
    (Env mappings parentEnv) <- getEnv
    let newEnv = mappings & Map.insert name (expression, exprEnv)
    setEnv (Env newEnv parentEnv)

bind :: String -> Expression -> Computation ()
bind name expression =
  -- ADD LAZINESS
  withTrace ("bind " ++ name ++ " = " ++ show expression) $ do
    env@(Env mappings parentEnv) <- getEnv
    let newEnv = mappings & Map.insert name (expression, env)
    setEnv (Env newEnv parentEnv)

readBindingExpression :: String -> Computation Expression
readBindingExpression name = do
  env@(Env mappings parent) <- getEnv
  let lookupRes = Map.lookup name mappings
  case (lookupRes, parent) of
    (Just (expr, _value), _) ->
      return expr
    (Nothing, Just parentEnv) ->
      runInEnv parentEnv (readBindingExpression name)
    (Nothing, Nothing) ->
      throwWithTrace RuntimeError ("name '" ++ name ++ "' not found. Env\n: " ++ show env)

readBinding :: String -> Computation Expression
readBinding name = do
  env@(Env mappings parent) <- getEnv
  let lookupRes = Map.lookup name mappings
  case (lookupRes, parent) of
    (Just (expr, exprEnv), _) ->
      runInEnv exprEnv (return expr)
    (Nothing, Just parentEnv) ->
      runInEnv parentEnv (readBinding name)
    (Nothing, Nothing) ->
      throwWithTrace RuntimeError ("name '" ++ name ++ "' not found. Env\n: " ++ show env)

-- | The default environment is not the empty environment!
defaultEnv :: Env
defaultEnv = emptyEnv

nativeFn :: String -> (Integer -> Integer -> Integer) -> Expression -> Expression -> Computation Expression
nativeFn fnName fn argA argB = do
  evalA <- traceEval argA
  evalB <- traceEval argB
  case (evalA, evalB) of
    (EInteger x, EInteger y) -> return $ EInteger (fn x y)
    (_, _) -> return $ Call (Name fnName) [evalA, evalB]

traceEval :: Expression -> Computation Expression
traceEval expr = do
  s <- curStack
  withTrace (show expr) $ eval (expr & debugPipe ("\ntrace:\n" ++ (s & reverse & map ("  . " ++) & unlines) ++ "expr"))

isCallable :: Expression -> Bool
isCallable (CapturedLambda {}) = True
isCallable _ = False

isValue :: Expression -> Bool
isValue (EInteger _) = True
isValue (EString _) = True
isValue (EBool _) = True
isValue (Quote _) = True
isValue (CapturedLambda {}) = True
-- isValue (Call (CapturedLambda lEnv [] body) _) = True
isValue _ = False

smallStep :: Expression -> Computation Expression
smallStep (Name n) = readBinding n
smallStep (Lambda argNames bodyExpr) = do
  env <- getEnv
  return $ CapturedLambda env argNames bodyExpr
smallStep (Call (Name "+") [EInteger x, EInteger y]) = return $ EInteger (x + y)
smallStep (Call (Name "+") [exprA, exprB])
  | not (isValue exprA) = do
      astep <- smallStep exprA
      return $ Call (Name "+") [astep, exprB]
  | not (isValue exprB) = do
      bstep <- smallStep exprB
      return $ Call (Name "+") [exprA, bstep]
  | otherwise = do
      throwWithTrace RuntimeError "Don't know how to + these values"
smallStep (Call (Name "-") [EInteger x, EInteger y]) = return $ EInteger (x - y)
smallStep (Call (Name "-") [exprA, exprB])
  | not (isValue exprA) = do
      astep <- smallStep exprA
      return $ Call (Name "-") [astep, exprB]
  | not (isValue exprB) = do
      bstep <- smallStep exprB
      return $ Call (Name "-") [exprA, bstep]
  | otherwise = do
      throwWithTrace RuntimeError "Don't know how to - these values"
smallStep (Call (Name "*") [EInteger x, EInteger y]) = return $ EInteger (x * y)
smallStep (Call (Name "*") [exprA, exprB])
  | not (isValue exprA) = do
      astep <- smallStep exprA
      return $ Call (Name "*") [astep, exprB]
  | not (isValue exprB) = do
      bstep <- smallStep exprB
      return $ Call (Name "*") [exprA, bstep]
  | otherwise = do
      return $ Call (Name "*") [exprA, exprB]
smallStep (Call (Name "/") [EInteger x, EInteger y]) = return $ EInteger (x `div` y)
smallStep (Call (Name "=") [exprA, exprB])
  | isValue exprA && isValue exprB = return $ EBool (exprA == exprB)
  | not (isValue exprA) = do
      stepA <- smallStep exprA
      return $ Call (Name "=") [stepA, exprB]
  | not (isValue exprB) = do
      stepB <- smallStep exprB
      return $ Call (Name "=") [exprA, stepB]
smallStep (Call (Name "eval") [Quote expr]) = smallStep expr
smallStep (Call (Name "eval") [expr]) = do
  exprStep <- smallStep expr
  return $ Call (Name "eval") [exprStep]
smallStep (Call (Name "enquote") [Name name]) = do
  expr <- readBinding name
  return $ Quote expr
smallStep (Call (CapturedLambda lEnv [] body) []) = do
  return $ InEnv lEnv body
smallStep expr@(Call (CapturedLambda lEnv [] body) args@(_ : _)) = do
  let newLambda = InEnv lEnv body
  -- throwWithTrace RuntimeError $ "too many args: " ++ show expr ++ "alt: " ++ show newLambda
  return $ Call newLambda args
smallStep (Call (CapturedLambda lEnv argNames@(_ : _) body) []) = do
  return (CapturedLambda lEnv argNames body)
smallStep (Call (CapturedLambda lEnv (n : ames) body) (a : rgs)) = do
  callerEnv <- getEnv
  newLEnv <- runInEnv lEnv $ do
    bind n (InEnv callerEnv a)
    getEnv
  return $ Call (CapturedLambda newLEnv ames body) rgs
smallStep expr@(Call fn args)
  | not (isValue fn) = do
      fnStep <- smallStep fn
      return $ Call fnStep args
  | otherwise = throwWithTrace RuntimeError $ "This part of calling not yet implemented" ++ show expr
smallStep (InEnv env expr) =
  if isValue expr
    then return expr
    else do
      stepExpr <- runInEnv env $ smallStep expr
      return $ InEnv env stepExpr
smallStep (IfElse (EBool True) tExpr _) = return tExpr
smallStep (IfElse (EBool False) _ fExpr) = return fExpr
smallStep expr@(IfElse condExpr tExpr fExpr) =
  if not (isValue condExpr)
    then do
      condStep <- smallStep condExpr
      return $ IfElse condStep tExpr fExpr
    else throwWithTrace RuntimeError $ "If badly formed: " ++ show expr
smallStep (Define name expr) = do
  bind name expr
  return $ Quote expr
smallStep expr = throwWithTrace RuntimeError $ "Not yet implemented: " ++ show expr

eval :: Expression -> Computation Expression
eval (Call (Name "+") [xExpr, yExpr]) = nativeFn "+" (+) xExpr yExpr
eval (Call (Name "-") [xExpr, yExpr]) = nativeFn "-" (-) xExpr yExpr
eval (Call (Name "*") [xExpr, yExpr]) = nativeFn "*" (*) xExpr yExpr
eval (Call (Name "/") [xExpr, yExpr]) = nativeFn "/" div xExpr yExpr
eval (Call (Name "%") [xExpr, yExpr]) = nativeFn "%" rem xExpr yExpr
eval (Call (Name "=") [xExpr, yExpr]) = do
  xValue <- traceEval (xExpr & debugPipe "= first arg expr")
  yValue <- traceEval yExpr
  case (xValue & debugPipe "= first arg value", yValue) of
    (EInteger x, EInteger y) -> return $ EBool (x == y)
    (EString x, EString y) -> return $ EBool (x == y)
    (Name x, Name y) -> return $ EBool (x == y)
    (EBool x, EBool y) -> return $ EBool (x == y)
    (Quote (Name x), Quote (Name y)) -> return $ EBool (x == y)
    (_, _) -> do throwWithTrace RuntimeError ("Don't know how to compare \"" ++ show xValue ++ "\" and \"" ++ show yValue ++ "\"")
eval (Quote expr) = return expr
eval (Call (Name "bindIn") [nameExpr, valueExpr, body]) = do
  nameValue <- traceEval nameExpr
  case nameValue of
    Name n ->
      runInChildEnv $ do
        bind n valueExpr
        traceEval body
    _ -> do throwWithTrace RuntimeError ("Error calling bind, name is " ++ show nameValue)
eval (Call (Name "bind") [nameExpr, valueExpr]) = do
  nameValue <- traceEval nameExpr
  valueVal <- traceEval valueExpr
  case nameValue of
    Name n -> do bind n valueVal; return valueExpr
    _ -> do throwWithTrace RuntimeError ("Error calling bind, name is " ++ show nameValue)
eval (Call (Name "head") [List (x : _)]) = return x
eval (Call (Name "head") [argExpr]) = do
  argValue <- traceEval argExpr
  traceEval $ Call (Name "head") [argValue]
-- TODO figure out a list semantic
eval (Call (Name "tail") [List (_ : [])]) = return (Name "empty")
eval (Call (Name "tail") [List (a : rgs)]) = return (List rgs)
eval (Call (Name "tail") [argExpr]) = do
  argValue <- traceEval argExpr
  traceEval $ Call (Name "tail") [argValue]
eval (Call (Name "enquote") [Name n]) = do
  res <- readBindingExpression n
  return res
eval (Call (Name "eval") [expr]) = do
  -- we need two evals here:
  -- one to eagerly evaluate the argument, which we always do
  res <- traceEval expr

  -- and one to actually do the "eval"
  traceEval res
eval (Let bindings expression) =
  runInChildEnv $ do
    foldM_ (\_ (name, value) -> do bind name value) () bindings
    traceEval expression
eval (Define name expression) = do
  -- Currently we eagerly evaluate
  evaluatedExpression <- traceEval expression
  bind name expression
  return evaluatedExpression
eval (Name x) =
  -- eager evaluation means we don't evaluate on lookup
  readBinding x
eval (IfElse condExpr trueExpr falseExpr) = do
  condValue <- traceEval condExpr
  case condValue of
    EBool True -> traceEval trueExpr
    EBool False -> traceEval falseExpr
    _ -> throwWithTrace RuntimeError ("Ifelse needs a boolean, but got \"" ++ show condValue ++ "\"")
eval (Lambda argNames bodyExpr) = do
  env <- getEnv
  return $ CapturedLambda env argNames bodyExpr
eval (Call callExpr argExprs) = do
  fn <- traceEval callExpr
  case fn of
    CapturedLambda env argNames body ->
      evalLambda argNames argExprs env body
    Name s ->
      eval (Call fn argExprs)
    _ ->
      throwWithTrace RuntimeError ("I don't know how to call: " ++ show fn)
eval expr@(EInteger _) = return expr
eval expr@(EString _) = return expr
eval expr@(List _) = return expr
eval expr = throwWithTrace RuntimeError ("Not yet implemented: " ++ show expr)

evalLambda :: [String] -> [Expression] -> Env -> Expression -> Computation Expression
evalLambda [] [] env body = runInEnv env $ traceEval body
evalLambda [] _ _ _ = throwWithTrace RuntimeError "Too many arguments"
evalLambda _ [] _ _ = throwWithTrace RuntimeError "Not enough arguments"
evalLambda (n : ns) (argExpr : as) env body =
  -- TODO arg needs to be evaluated in current env
  let newbody = Let [(n, argExpr)] body
   in evalLambda ns as env newbody

-------- Main ---------

showWithError :: Either Error String -> String
showWithError res =
  case res of
    Right expr -> expr
    Left err -> "error: " ++ show err

evalManyStrings :: String -> [String] -> Computation String
evalManyStrings final [] = pure final
evalManyStrings str (c : cs) = do
  res <- catchE (rep c) (\err -> return (show err))
  evalManyStrings (str ++ "\n\n> " ++ c ++ "\n" ++ res) cs

manySteps :: Int -> Expression -> Computation [Expression]
manySteps maxSteps expr =
  if maxSteps <= 0
    then return [expr]
    else do
      withTrace (show expr) $ -- eval (expr & debugPipe ("\ntrace:\n" ++ (s & reverse & map ("  . " ++) & unlines) ++ "expr"))
        if isValue expr
          then return [expr]
          else do
            stepExpr <- smallStep expr
            if stepExpr == expr
              then return [expr]
              else do
                nextSteps <- manySteps (maxSteps - 1) stepExpr
                return (expr : nextSteps)

rep :: String -> Computation String
rep input =
  let parseRes =
        input
          & Parsec.parse parseTopExpression "(source)"
   in case parseRes of
        Right expr -> do
          steps <- manySteps 100 expr
          return $
            -- "parsed: "
            --   ++ show expr
            --   ++ "\n"
            (map (("  " ++) . show) steps & unlines)
        Left err -> do
          return $ "error " ++ show err

repl :: Env -> IO ()
repl env = do
  putStr "\n> "
  hFlush stdout
  input <- getLine
  if null input
    then return ()
    else do
      let (errorfulRes, resEnv) = compute env (rep input)
      putStrLn (showWithError errorfulRes)
      repl resEnv

main :: IO ()
main =
  let test_cases =
        [ "2",
          "(+ 2 1)",
          "(+ 2 (* 3 5))",
          "(define name \"olivia\")",
          "name",
          "(define x 5)",
          "x",
          "(quote x)",
          "(eval (quote x))",
          "(+ x 1)",
          "((lambda (x) (* x x)) 3)",
          "(define y (+ x 2))",
          "(+ x y)",
          "(+ x (* y 3))",
          -- "(let ((a 1)) a)",
          -- "(let ((z 12)) (/ z 4))",
          -- "z",
          "(lambda (arg) (* arg arg))",
          "((lambda (arg) (* arg arg)) 5)",
          "arg",
          "(define square (lambda (arg) (* arg arg)))",
          "(square (quote x))",
          "square",
          "(square)",
          "(square x y)",
          "(square x)",
          "(square z)",
          "(square x)",
          "(define mass (quote m))",
          "mass",
          "m",
          "(eval mass)",
          "(define m 88)",
          "mass",
          "(eval mass)",
          "(quote (square x))",
          "(* (quote height) (quote mass))",
          "(* x (quote mass))",
          "(square (quote x))",
          -- "(eval (quote (square x)))",
          -- "((eval (quote square)) x)",
          -- "(let ((z 12)) x)",
          "(define addToX (lambda (inc) (+ x inc)))",
          "(addToX 3)",
          "(define ke (lambda (mass velocity) (/ (* mass (* velocity velocity)) 2)))",
          -- "(ke (quote m) 2)",
          -- "(ke (quote m) (quote v))",
          -- "(define capture (lambda (fn) (enquote fn)))",
          -- "(capture ke)",
          "(define plus (lambda (x y) (+ x y)))",
          "(plus 2 3)",
          -- "(define isPlus (lambda (fn) (= (enquote fn) (quote plus))))",
          -- "(isPlus plus)",
          -- "(isPlus ke)",
          -- "(define ycomb (lambda (fn) ((lambda (x) (fn x x)) (lambda (x) (fn x x)))  ))",
          "(define add (lambda (a) (lambda (b) (+ b a))))",
          "(add 2 3)",
          "(define inc (add 1))",
          "(inc 2)",
          "(define ycomb (lambda (fn) ((lambda (x) (fn (lambda (y) (x x y)))) (lambda (x) (fn (lambda (y) (x x y)))))  ))",
          "(define factHelper (lambda (factRec n) (if (= n 0) 1 (* n (factRec (- n 1))))))",
          "(define fact (ycomb factHelper))",
          "(fact 0)",
          "(fact 1)",
          -- "(bind (quote boundName) 1)",
          -- "boundName",
          -- "(define xs (list 1 2 3))",
          -- "(head xs)",
          -- "(tail xs)",
          -- "(define defun (lambda (fnName argName body) (bind fnName (quote (lambda (argValue) (bindIn argName argValue (eval body)))))))",
          -- "(defun (quote s) (quote num) (quote (+ num 97)))",
          -- "(bind (quote v) 3)",
          -- "v",
          -- "(define myBind (lambda (name value) ((quote bind) (enquote name) value)))",
          -- "(eval ((quote bind) (quote t) 5))",
          -- "(myBind u 5)",
          -- "u",
          -- "(define tBind (myBind (quote t) 5))",
          -- "(eval (eval tBind))",
          -- "t",
          -- "(bind (quote s) square)",
          -- "(define s square)",
          -- "(s 3)",
          -- "((eval s) 3)",
          -- "(enquote s)",
          "\"done\""
        ]

      evaluations :: Computation String
      evaluations = evalManyStrings "Starting autoevaluation...\n" test_cases

      finalRes :: Either Error String
      (finalRes, finalEnv) = compute defaultEnv evaluations
   in do
        putStrLn ""
        -- putStr (concatMap (\(expr, res) -> "> " ++ expr ++ "\n\t" ++ show res ++ "\n\n") parsedExpressions)
        putStr (showWithError finalRes)
        putStrLn ""

        repl finalEnv
        putStrLn "done"
