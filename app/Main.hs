{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Use tuple-section" #-}
module Main (main) where

import Control.Applicative
import Control.Monad (foldM, foldM_, liftM)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import qualified Data.Either as Either
import Data.Function
import qualified Data.Map as Map
import Debug.Trace
import Parser
import System.IO
import qualified Text.Parsec as Parsec

debugPipe :: (Show b) => String -> b -> b
debugPipe name x = trace (name ++ ": " ++ show x) x

newtype Computation a = InnerCompute (Env -> (Env, a))

data Error
  = ParseError String
  | RuntimeError String
  deriving (Show)

type ErrorfullComputation a = ExceptT Error Computation a

instance Functor Computation where
  -- fmap :: (a -> b) -> Computation a -> Computation b
  fmap = liftM

instance Applicative Computation where
  -- pure :: a -> Computation a
  pure x = InnerCompute (\env -> (env, x))

  -- <*> :: Computation (a -> b) -> Computation a -> Computation b
  (InnerCompute computeFn) <*> (InnerCompute computeArg) =
    InnerCompute
      ( \env ->
          let (argEnv, arg) = computeArg env
              -- TODO : what env should fn be evaluated in?
              (fnEnv, concreteFn) = computeFn argEnv
           in (fnEnv, concreteFn arg)
      )

instance Monad Computation where
  -- >>= (Computation a) -> (a -> Computation b) -> (Computation b)
  (InnerCompute computeA) >>= fn =
    InnerCompute
      ( \env ->
          let -- get argument
              (envA, a) = computeA env
              -- get, and unpack the next computation
              InnerCompute computeB = fn a
           in -- execute the computation
              computeB envA
      )

-- | Base monad operations
compute :: Env -> Computation a -> (Env, a)
compute env (InnerCompute fn) = fn env

getEnv :: Computation Env
getEnv =
  InnerCompute (\env -> (env, env))

setEnv :: Env -> Computation ()
setEnv newEnv =
  InnerCompute (\_ -> (newEnv, ()))

setEnvForComputation :: Env -> Computation a -> Computation a
setEnvForComputation otherEnv comp = do
  initialEnv <- getEnv
  setEnv otherEnv
  res <- comp
  setEnv initialEnv
  return res

-- | Error monad base operations
computeWithErrors :: Env -> ErrorfullComputation a -> (Env, Either Error a)
computeWithErrors env comp = compute env (runExceptT comp)

liftOp :: Computation a -> ErrorfullComputation a
liftOp comp =
  ExceptT
    ( do
        res <- comp
        return $ Right res
    )

getEnvWithErrors :: ErrorfullComputation Env
getEnvWithErrors = liftOp getEnv

setEnvWithErrors :: Env -> ErrorfullComputation ()
setEnvWithErrors = liftOp . setEnv

setEnvForComputationWithErrors :: Env -> ErrorfullComputation a -> ErrorfullComputation a
setEnvForComputationWithErrors env comp =
  let (_, res) = computeWithErrors env comp
   in ExceptT (return res)

emptyEnv :: Env
emptyEnv = Env Map.empty Nothing

getNewEnv :: Env -> Env
getNewEnv parentEnv = Env Map.empty (Just parentEnv)

inChildEnv :: ErrorfullComputation a -> ErrorfullComputation a
inChildEnv comp = do
  env <- getEnvWithErrors
  let childEnv = getNewEnv env
  setEnvForComputationWithErrors childEnv comp

bind :: String -> Token -> ErrorfullComputation ()
bind name expression = do
  (Env mappings parentEnv) <- getEnvWithErrors
  value <- eval expression
  let newEnv = mappings & Map.insert name (expression, value)
  setEnvWithErrors (Env newEnv parentEnv)

readBindingExpression :: String -> ErrorfullComputation Token
readBindingExpression name = do
  (Env mappings parent) <- getEnvWithErrors
  let lookupRes = Map.lookup name mappings
  case (lookupRes, parent) of
    (Just (expr, _value), _) -> return expr
    (Nothing, Just parentEnv) -> do
      setEnvForComputationWithErrors parentEnv (readBindingExpression name)
    (Nothing, Nothing) -> throwE $ RuntimeError ("name '" ++ name ++ "' not found")

readBinding :: String -> ErrorfullComputation Token
readBinding name = do
  (Env mappings parent) <- getEnvWithErrors
  let lookupRes = Map.lookup name mappings
  case (lookupRes, parent) of
    (Just (_expr, value), _) -> return value
    (Nothing, Just parentEnv) -> do
      setEnvForComputationWithErrors parentEnv (readBinding name)
    (Nothing, Nothing) -> throwE $ RuntimeError ("name '" ++ name ++ "' not found")

-- | The default environment is not the empty environment!
defaultEnv :: Env
defaultEnv = emptyEnv

nativeFn :: String -> (Integer -> Integer -> Integer) -> Token -> Token -> ErrorfullComputation Token
nativeFn fnName fn argA argB = do
  evalA <- eval argA
  evalB <- eval argB
  case (evalA, evalB) of
    (EInteger x, EInteger y) -> return $ EInteger (fn x y)
    (_, _) -> return $ Call (Name fnName) [evalA, evalB]

eval :: Token -> ErrorfullComputation Token
eval (Call (Name "+") [xExpr, yExpr]) = nativeFn "+" (+) xExpr yExpr
eval (Call (Name "-") [xExpr, yExpr]) = nativeFn "-" (-) xExpr yExpr
eval (Call (Name "*") [xExpr, yExpr]) = nativeFn "*" (*) xExpr yExpr
eval (Call (Name "/") [xExpr, yExpr]) = nativeFn "/" div xExpr yExpr
eval (Call (Name "%") [xExpr, yExpr]) = nativeFn "%" rem xExpr yExpr
eval (Call (Name "=") [xExpr, yExpr]) = do
  xValue <- eval (xExpr & debugPipe "= first arg expr")
  yValue <- eval yExpr
  case (xValue & debugPipe "= first arg value", yValue) of
    (EInteger x, EInteger y) -> return $ EBool (x == y)
    (EString x, EString y) -> return $ EBool (x == y)
    (Name x, Name y) -> return $ EBool (x == y)
    (EBool x, EBool y) -> return $ EBool (x == y)
    (Quote (Name x), Quote (Name y)) -> return $ EBool (x == y)
    (_, _) -> do throwE $ RuntimeError $ "Don't know how to compare \"" ++ show xValue ++ "\" and \"" ++ show yValue ++ "\""
eval (Quote expr) = return expr
eval (Call (Name "bindIn") [nameExpr, valueExpr, body]) = do
  nameValue <- eval nameExpr
  case nameValue of
    Name n ->
      do
        bind n valueExpr
        eval body
    _ -> do throwE $ RuntimeError ("Error calling bind, name is " ++ show nameValue)
eval (Call (Name "bind") [nameExpr, valueExpr]) = do
  nameValue <- eval nameExpr
  case nameValue of
    Name n -> do bind n valueExpr; return valueExpr
    _ -> do throwE $ RuntimeError ("Error calling bind, name is " ++ show nameValue)
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
  res <- eval expr

  -- and one to actually do the "eval"
  eval res
eval (Let bindings expression) =
  inChildEnv $ do
    foldM_ (\_ (name, value) -> do bind name value) () bindings
    eval expression
eval (Define name expression) = do
  -- Currently we eagerly evaluate
  evaluatedExpression <- eval expression
  bind name expression
  return evaluatedExpression
eval (Name x) =
  -- eager evaluation means we don't evaluate on lookup
  readBinding x
eval (IfElse condExpr trueExpr falseExpr) = do
  condValue <- eval condExpr
  case condValue of
    EBool True -> eval trueExpr
    EBool False -> eval falseExpr
    _ -> throwE $ RuntimeError ("Ifelse needs a boolean, but got \"" ++ show condValue ++ "\"")
eval (Lambda argNames bodyExpr) = do
  env <- getEnvWithErrors
  return $ CapturedLambda env argNames bodyExpr
eval (Call callExpr argExprs) = do
  fn <- eval callExpr
  case fn of
    CapturedLambda env argNames body ->
      evalLambda argNames argExprs env body
    _ ->
      throwE (RuntimeError ("I don't know how to call: " ++ show fn))
eval (EInteger x) = return $ EInteger x
eval (EString s) = return $ EString s
eval expr = throwE $ RuntimeError ("Not yet implemented: " ++ show expr)

evalLambda :: [String] -> [Token] -> Env -> Token -> ErrorfullComputation Token
evalLambda [] [] env body = setEnvForComputationWithErrors env $ eval body
evalLambda [] _ _ _ = throwE $ RuntimeError "Too many arguments"
evalLambda _ [] _ _ = throwE $ RuntimeError "Not enough arguments"
evalLambda (n : ns) (argExpr : as) env body =
  let newbody = Let [(n, argExpr)] body
   in evalLambda ns as env newbody

-------- Main ---------

showWithError :: Either Error String -> String
showWithError res =
  case res of
    Right expr -> expr
    Left err -> "error: " ++ show err

evalManyStrings :: String -> [String] -> ErrorfullComputation String
evalManyStrings final [] = pure final
evalManyStrings str (c : cs) = do
  res <-
    catchE
      (rep c)
      ( \err ->
          ExceptT (do return $ Right (show err))
      )
  evalManyStrings (str ++ "\n\n> " ++ c ++ "\n" ++ res) cs

rep :: String -> ErrorfullComputation String
rep input =
  let parseRes =
        input
          & Parsec.parse parseTopExpression "(source)"
   in case parseRes of
        Right expr -> do
          res <- eval expr
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
      let (resEnv, errorfulRes) = computeWithErrors env (rep input)
      print (showWithError errorfulRes)
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
          "square",
          "(square)",
          "(square x y)",
          "(square x)",
          "(square z)",
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

      evaluations :: ErrorfullComputation String
      evaluations = evalManyStrings "Starting autoevaluation...\n" test_cases

      finalRes :: Either Error String
      (finalEnv, finalRes) = computeWithErrors defaultEnv evaluations
   in do
        putStrLn ""
        -- putStr (concatMap (\(expr, res) -> "> " ++ expr ++ "\n\t" ++ show res ++ "\n\n") parsedExpressions)
        putStr (showWithError finalRes)

        repl finalEnv
        putStrLn "done"
