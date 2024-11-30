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

-- TODO make sure failures during executing in a different env does not screw return env
type Computation a = (ExceptT Error (ReaderT [String] (State Env))) a

-- | Error monad base operations
compute :: Env -> Computation a -> (Either Error a, Env)
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

bind :: String -> Expression -> Computation ()
bind name expression =
  -- ADD LAZINESS
  withTrace ("bind " ++ name ++ " = " ++ show expression) $ do
    (Env mappings parentEnv) <- getEnv
    let newEnv = mappings & Map.insert name expression
    setEnv (Env newEnv parentEnv)

readBinding :: String -> Computation Expression
readBinding name = do
  env@(Env mappings parent) <- getEnv
  let lookupRes = Map.lookup name mappings
  case (lookupRes, parent) of
    (Just expr, _) ->
      return expr
    (Nothing, Just parentEnv) ->
      runInEnv parentEnv (readBinding name)
    (Nothing, Nothing) ->
      throwWithTrace RuntimeError ("name '" ++ name ++ "' not found. Env\n: " ++ show env)

-- | The default environment is not the empty environment!
defaultEnv :: Env
defaultEnv = emptyEnv

-- nativeFn :: String -> (Integer -> Integer -> Integer) -> Expression -> Expression -> Computation Expression
-- nativeFn fnName fn argA argB = do
--   evalA <- traceEval argA
--   evalB <- traceEval argB
--   case (evalA, evalB) of
--     (EInteger x, EInteger y) -> return $ EInteger (fn x y)
--     (_, _) -> return $ Call (Name fnName) [evalA, evalB]

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
smallStep (Call (Name "bind") [Name name, expr]) = do
  bind name expr
  return $ Quote expr
smallStep (Call (Name "bind") [nameExpr, expr]) = do
  nameStep <- smallStep nameExpr
  return $ Call (Name "bind") [nameStep, expr]
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
smallStep (Quote expr) = return expr
smallStep (Define name expr) = do
  bind name expr
  return $ Quote expr
smallStep expr = throwWithTrace RuntimeError $ "Not yet implemented: " ++ show expr

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
          -- "(fact 1)",
          "(bind (quote boundName) 1)",
          "boundName",
          -- "(define xs (list 1 2 3))",
          -- "(head xs)",
          -- "(tail xs)",
          -- "(define defun (lambda (argName body) (bind (enquote fnName) (lambda (argValue) (bindIn argName argValue (eval body))))))",
          -- "(defun (quote num) (quote (+ num 97)))",
          -- "s",
          "(bind (quote v) 3)",
          "v",
          -- "(define myBind (lambda (name value) ((quote bind) (enquote name) value)))",
          -- "(eval ((quote bind) (quote t) 5))",
          -- "(myBind u 5)",
          -- "u",
          -- "(define tBind (myBind (quote t) 5))",
          -- "(eval (eval tBind))",
          -- "t",
          -- "(bind (quote s) square)",
          "(define s square)",
          "(s 3)",
          -- "((eval s) 3)",
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
