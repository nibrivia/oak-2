{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Main (main) where

import Control.Applicative
import Control.Monad (foldM, foldM_, liftM)
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

instance Functor Computation where
  -- fmap :: (a -> b) -> Computation a -> Computation b
  fmap = liftM

instance Applicative Computation where
  -- pure :: a -> Computation a
  pure x = Computation (\env -> (env, x))

  -- <*> :: Computation (a -> b) -> Computation a -> Computation b
  (Computation computeFn) <*> (Computation computeArg) =
    Computation
      ( \env ->
          let (argEnv, arg) = computeArg env
              -- TODO : what env should fn be evaluated in?
              (fnEnv, concreteFn) = computeFn argEnv
           in (fnEnv, concreteFn arg)
      )

instance Monad Computation where
  -- >>= (Computation a) -> (a -> Computation b) -> (Computation b)
  (Computation computeA) >>= fn =
    Computation
      ( \env ->
          let -- get argument
              (envA, a) = computeA env
              -- get, and unpack the next computation
              Computation computeB = fn a
           in -- execute the computation
              computeB envA
      )

-- | Runs a computation in a specific env
compute :: Env -> Computation a -> (Env, a)
compute env (Computation fn) = fn env

computeRes :: Env -> Computation a -> a
computeRes env computation = let (_, res) = compute env computation in res

emptyEnv :: Env
emptyEnv = Env Map.empty Nothing

getNewEnv :: Env -> Env
getNewEnv parentEnv = Env Map.empty (Just parentEnv)

inChildEnv :: Computation a -> Computation a
inChildEnv comp =
  Computation
    ( \parentEnv ->
        let childEnv = getNewEnv parentEnv
         in (parentEnv, computeRes childEnv comp)
    )

currentEnv :: Computation Env
currentEnv =
  Computation (\env -> (env, env))

inOtherEnv :: Env -> Computation a -> Computation a
inOtherEnv otherEnv comp =
  Computation (\env -> (env, computeRes otherEnv comp))

bind :: String -> Token -> Computation ()
bind name expression =
  Computation
    ( \env@(Env mappings parentEnv) ->
        let value = computeRes env (eval expression)
         in (Env (mappings & Map.insert name (expression, value)) parentEnv, ())
    )

readBindingExpression :: String -> Computation Token
readBindingExpression name =
  Computation
    ( \env@(Env mappings parent) ->
        let lookupRes = Map.lookup name mappings
         in case (lookupRes, parent) of
              (Just (expr, _value), _) -> (env, expr)
              (Nothing, Just parentEnv) -> (env, computeRes parentEnv (readBindingExpression name))
              (Nothing, Nothing) -> (env, ParseError ("name '" ++ name ++ "' not found"))
    )

readBinding :: String -> Computation Token
readBinding name =
  Computation
    ( \env@(Env mappings parent) ->
        let lookupRes = Map.lookup name mappings
         in case (lookupRes, parent) of
              (Just (_expr, value), _) -> (env, value)
              (Nothing, Just parentEnv) -> (env, computeRes parentEnv (readBinding name))
              (Nothing, Nothing) -> (env, ParseError ("name '" ++ name ++ "' not found"))
    )

-- | The default environment is not the empty environment!
defaultEnv :: Env
defaultEnv = emptyEnv

evalManyStrings :: String -> [String] -> Computation String
evalManyStrings final [] = pure final
evalManyStrings str (c : cs) = do
  res <- rep c
  evalManyStrings (str ++ "\n\n> " ++ c ++ "\n" ++ res) cs

rep :: String -> Computation String
rep input =
  let expr =
        input
          & Parsec.parse parseTopExpression "(source)"
          & Either.either (\err -> err & show & ParseError) id
   in do
        res <- eval expr
        return $
          ""
            ++ "parsed: "
            ++ show expr
            ++ "\n"
            ++ "eval  : "
            ++ show res

repl :: Env -> IO ()
repl env = do
  putStr "\n> "
  hFlush stdout
  input <- getLine
  if null input
    then return ()
    else do
      let (resEnv, res) = compute env (rep input)
      putStrLn res
      repl resEnv

nativeFn :: String -> (Integer -> Integer -> Integer) -> Token -> Token -> Computation Token
nativeFn fnName fn argA argB = do
  evalA <- eval argA
  evalB <- eval argB
  case (evalA, evalB) of
    (EInteger x, EInteger y) -> return $ EInteger (fn x y)
    (_, _) -> return $ Call (Name fnName) [evalA, evalB]

eval :: Token -> Computation Token
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
    (_, _) -> return $ ParseError $ "Don't know how to compare \"" ++ show xValue ++ "\" and \"" ++ show yValue ++ "\""
eval (Quote expr) = return expr
eval (Call (Name "bindIn") [nameExpr, valueExpr, body]) = do
  nameValue <- eval nameExpr
  case nameValue of
    Name n ->
      do
        bind n valueExpr
        eval body
    _ -> return $ ParseError ("Error calling bind, name is " ++ show nameValue)
eval (Call (Name "bind") [nameExpr, valueExpr]) = do
  nameValue <- eval nameExpr
  case nameValue of
    Name n -> do bind n valueExpr; return valueExpr
    _ -> return $ ParseError ("Error calling bind, name is " ++ show nameValue)
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
    _ -> return $ ParseError ("Ifelse needs a boolean, but got \"" ++ show condValue ++ "\"")
eval (Lambda args bodyExpr) = do
  env <- currentEnv
  return $ CapturedLambda env (evalLambda args bodyExpr)
eval (Call callExpr argExprs) = do
  fn <- eval callExpr
  case fn of
    CapturedLambda env fnComputation -> inOtherEnv env (eval (fnComputation argExprs))
    _ ->
      pure (ParseError ("I don't know how to call: " ++ show fn))
eval (EInteger x) = return $ EInteger x
eval (EString s) = return $ EString s
eval expr = return $ ParseError ("Not yet implemented: " ++ show expr)

evalLambda :: [String] -> Token -> [Token] -> Token
evalLambda [] body [] = body
evalLambda [] _ _ = ParseError "Too many arguments"
evalLambda _ _ [] = ParseError "Not enough arguments"
evalLambda (n : ns) body (argExpr : as) =
  let newbody = Let [(n, argExpr)] body
   in evalLambda ns newbody as

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
          "(define defun (lambda (argName body) (lambda (argValue) (bindIn (head (eval (enquote argName))) argValue body))))",
          "(define s (defun (num) (+ num num)))",
          "(s 3)",
          "((eval s) 3)",
          "(enquote s)",
          "\"done\""
        ]

      evaluations :: Computation String
      evaluations = evalManyStrings "Starting autoevaluation...\n" test_cases

      finalRes :: String
      (finalEnv, finalRes) = compute defaultEnv evaluations
   in do
        putStrLn ""
        -- putStr (concatMap (\(expr, res) -> "> " ++ expr ++ "\n\t" ++ show res ++ "\n\n") parsedExpressions)
        putStrLn finalRes

        repl finalEnv
        putStrLn "done"
