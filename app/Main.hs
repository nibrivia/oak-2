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
    show eType ++ ": " ++ msg ++ " in:\n" ++ (sTrace & map ("    " ++) & reverse & unlines)

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
  cur_stack <- lift ask
  mapExceptT (local (const (cur_stack ++ [str]))) comp

throwWithTrace :: ErrorType -> String -> Computation a
throwWithTrace errType msg = do
  cur_stack <- lift ask
  let new_err = Error {errorType = errType, message = msg, stack = cur_stack}
  throwE new_err

runInEnv :: Env -> Computation a -> Computation a
runInEnv env comp = do
  cur_env <- getEnv
  setEnv env
  finallyE (comp) (setEnv cur_env)

emptyEnv :: Env
emptyEnv = Env Map.empty Nothing

runInChildEnv :: Computation a -> Computation a
runInChildEnv comp = do
  env <- getEnv
  let childEnv = makeChildEnv env
  runInEnv childEnv comp

bind :: String -> Token -> Computation ()
bind name expression = do
  (Env mappings parentEnv) <- getEnv
  value <- eval expression
  let newEnv = mappings & Map.insert name (expression, value)
  setEnv (Env newEnv parentEnv)

readBindingExpression :: String -> Computation Token
readBindingExpression name = do
  (Env mappings parent) <- getEnv
  let lookupRes = Map.lookup name mappings
  case (lookupRes, parent) of
    (Just (expr, _value), _) ->
      return expr
    (Nothing, Just parentEnv) ->
      runInEnv parentEnv (readBindingExpression name)
    (Nothing, Nothing) ->
      throwWithTrace RuntimeError ("name '" ++ name ++ "' not found")

readBinding :: String -> Computation Token
readBinding name = do
  (Env mappings parent) <- getEnv
  let lookupRes = Map.lookup name mappings
  case (lookupRes, parent) of
    (Just (_expr, value), _) ->
      return value
    (Nothing, Just parentEnv) ->
      runInEnv parentEnv (readBinding name)
    (Nothing, Nothing) ->
      throwWithTrace RuntimeError ("name '" ++ name ++ "' not found")

-- | The default environment is not the empty environment!
defaultEnv :: Env
defaultEnv = emptyEnv

nativeFn :: String -> (Integer -> Integer -> Integer) -> Token -> Token -> Computation Token
nativeFn fnName fn argA argB = do
  evalA <- eval argA
  evalB <- eval argB
  case (evalA, evalB) of
    (EInteger x, EInteger y) -> return $ EInteger (fn x y)
    (_, _) -> return $ Call (Name fnName) [evalA, evalB]

traceEval :: Token -> Computation Token
traceEval expr = withTrace (show expr) $ eval expr

eval :: Token -> Computation Token
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
      do
        bind n valueExpr
        traceEval body
    _ -> do throwWithTrace RuntimeError ("Error calling bind, name is " ++ show nameValue)
eval (Call (Name "bind") [nameExpr, valueExpr]) = do
  nameValue <- traceEval nameExpr
  case nameValue of
    Name n -> do bind n valueExpr; return valueExpr
    _ -> do throwWithTrace RuntimeError ("Error calling bind, name is " ++ show nameValue)
eval (Call (Name "head") [Call callFn _]) = return callFn
-- TODO figure out a list semantic
eval (Call (Name "tail") [Call _ []]) = return (Name "empty")
eval (Call (Name "tail") [Call _ (a : rgs)]) = return (Call a rgs)
eval (Call (Name "enquote") [Name n]) = do
  res <- readBindingExpression n
  return $ Quote res
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
    _ ->
      throwWithTrace RuntimeError ("I don't know how to call: " ++ show fn)
eval (EInteger x) = return $ EInteger x
eval (EString s) = return $ EString s
eval expr = throwWithTrace RuntimeError ("Not yet implemented: " ++ show expr)

evalLambda :: [String] -> [Token] -> Env -> Token -> Computation Token
evalLambda [] [] env body = runInEnv env $ traceEval body
evalLambda [] _ _ _ = throwWithTrace RuntimeError "Too many arguments"
evalLambda _ [] _ _ = throwWithTrace RuntimeError "Not enough arguments"
evalLambda (n : ns) (argExpr : as) env body =
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

rep :: String -> Computation String
rep input =
  let parseRes =
        input
          & Parsec.parse parseTopExpression "(source)"
   in case parseRes of
        Right expr -> do
          res <- traceEval expr
          return $
            "parsed: "
              ++ show expr
              ++ "\n"
              ++ "eval  : "
              ++ show res
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
          "(define name \"olivia\")",
          "name",
          "(define x 5)",
          "x",
          "(quote x)",
          "(eval (quote x))",
          "(+ x 1)",
          "(define y (+ x 2))",
          "(+ x y)",
          "(+ x (* y 3))",
          "(let ((a 1)) a)",
          "(let ((z 12)) (/ z 4))",
          "z",
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
          "(eval (quote (square x)))",
          "((eval (quote square)) x)",
          "(let ((z 12)) x)",
          "(define addToX (lambda (inc) (+ x inc)))",
          "(addToX 3)",
          "(define ke (lambda (mass velocity) (/ (* mass (* velocity velocity)) 2)))",
          "(ke (quote m) 2)",
          "(ke (quote m) (quote v))",
          "(define capture (lambda (fn) (enquote fn)))",
          "(capture ke)",
          "(define plus (lambda (x y) (+ x y)))",
          "(define isPlus (lambda (fn) (= (enquote fn) (quote (quote plus)))))",
          "(isPlus plus)",
          "(isPlus ke)",
          "(define fact (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))))",
          "(fact 0)",
          "(fact 1)",
          "(bind (quote boundName) 1)",
          "boundName",
          "(define add (lambda (a) (lambda (b) (+ b a))))",
          "(define inc (add 1))",
          "(inc 2)",
          "(define defun (lambda (argName body) (lambda (argValue) (bindIn (head (eval (enquote argName))) argValue (enquote body)))))",
          "(define s (defun (quote num) (+ num 97)))",
          "(s 3)",
          "((eval s) 3)",
          "(enquote s)",
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
