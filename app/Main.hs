module Main (main) where

import Control.Applicative
import Control.Monad (ap, foldM, foldM_, liftM)
import qualified Data.Either as Either
import Data.Function
import Data.List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Debug.Trace
import Text.Parsec ((<?>))
import qualified Text.Parsec as Parsec

data Expression
  = EInteger Integer
  | EString String
  | Name String
  | Lambda [String] Expression
  | CapturedLambda ([Expression] -> Computation Expression)
  | Quote Expression
  | IfElse Expression Expression Expression
  | Define String Expression
  | DefineType String Expression
  | Call Expression [Expression]
  | RuntimeError String

instance Show Expression where
  show (EInteger x) = show x
  show (EString s) = "\"" ++ s ++ "\""
  show (Name s) = s
  show (Lambda args body) = "(lambda (" ++ (map show args & unwords) ++ ") " ++ show body ++ ")"
  show (CapturedLambda _) = "<captured lambda>"
  show (Quote expr) = "(quote " ++ show expr ++ ")"
  show (Define name expr) = "(define " ++ name ++ " " ++ show expr ++ ")"
  show (Call fn args) = "(" ++ show fn ++ " " ++ (args & map show & unwords) ++ ")"
  show (RuntimeError err) = "Error: " ++ err
  show _ = "unknown expression"

parseName :: Parsec.Parsec String () Expression
parseName = do
  name_str <-
    Parsec.string "+"
      <|> Parsec.string "*"
      <|> Parsec.string "/"
      <|> Parsec.string "-"
      <|> Parsec.string "%"
      <|> Parsec.many1 Parsec.letter
  return (Name name_str)

parseString :: Parsec.Parsec String () Expression
parseString = do
  _ <- Parsec.char '"'
  str <- Parsec.manyTill Parsec.anyChar (Parsec.char '"')
  return (EString str)

parseInt :: Parsec.Parsec String () Expression
parseInt = do
  integer_str <- Parsec.many1 Parsec.digit
  return (EInteger (read integer_str))

parseCall :: Parsec.Parsec String () Expression
parseCall = do
  openCall
  name <- parseExpression
  arguments <-
    Parsec.many
      ( do
          separator
          parseExpression
      )
  closeCall
  return (Call name arguments)

parseLambda :: Parsec.Parsec String () Expression
parseLambda = do
  openCall
  parseKeyword "lambda"
  separator
  openCall
  args <- (Parsec.many1 Parsec.letter) `Parsec.sepBy` separator
  closeCall
  separator
  body <- parseExpression
  closeCall
  return (Lambda args body)

closeCall :: Parsec.Parsec String () ()
closeCall = do
  Parsec.spaces
  _ <- Parsec.char ')'
  return ()

openCall :: Parsec.Parsec String () ()
openCall = do
  _ <- Parsec.char '('
  Parsec.spaces
  return ()

parseKeyword :: String -> Parsec.Parsec String () ()
parseKeyword keyword = do
  _ <- Parsec.string keyword
  return ()

separator :: Parsec.Parsec String () ()
separator = do
  _ <- Parsec.many1 Parsec.space
  return ()

parseDefineType :: Parsec.Parsec String () Expression
parseDefineType = do
  openCall
  parseKeyword "defineType"
  separator
  name <- Parsec.many1 Parsec.letter
  separator
  value <- parseExpression
  closeCall
  return (DefineType name value)

parseIfElse :: Parsec.Parsec String () Expression
parseIfElse = do
  openCall
  parseKeyword "if"
  separator
  condExpr <- parseExpression
  separator
  trueExpr <- parseExpression
  separator
  falseExpr <- parseExpression
  closeCall
  return (IfElse condExpr trueExpr falseExpr)

parseDefine :: Parsec.Parsec String () Expression
parseDefine = do
  openCall
  parseKeyword "define"
  separator
  name <- Parsec.many1 Parsec.letter
  separator
  value <- parseExpression
  closeCall
  return (Define name value)

parseQuote :: Parsec.Parsec String () Expression
parseQuote = do
  openCall
  _ <- Parsec.string "quote"
  separator
  expression <- parseExpression
  closeCall
  return (Quote expression)

parseExpression :: Parsec.Parsec String () Expression
parseExpression =
  parseInt
    <|> parseString
    <|> parseName
    <|> Parsec.try parseLambda
    <|> Parsec.try parseDefine
    <|> Parsec.try parseDefineType
    <|> Parsec.try parseQuote
    <|> Parsec.try parseIfElse
    <|> parseCall

parseTopExpression :: Parsec.Parsec String () Expression
parseTopExpression = do
  expr <- parseExpression
  Parsec.eof
  return expr

--------------------------------
-- Evaluation

data Env = Env (Map.Map String Expression) (Maybe Env)

emptyEnv :: Env
emptyEnv = Env Map.empty Nothing

makeChildEnv :: Env -> Env
makeChildEnv parentEnv = Env Map.empty (Just parentEnv)

bind :: String -> Expression -> Computation ()
bind name expression =
  Computation
    ( \(Env mappings parentEnv) ->
        (Env (mappings & Map.insert name expression) parentEnv, ())
    )

readBinding :: String -> Computation Expression
readBinding name =
  Computation
    ( \env@(Env mappings parent) ->
        let lookupRes = Map.lookup name mappings
         in case (lookupRes, parent) of
              (Just value, _) -> (env, value)
              (Nothing, Just parentEnv) -> compute parentEnv (readBinding name)
              (Nothing, Nothing) -> (env, RuntimeError "name not found")
    )

-- | The default environment is not the empty environment!
defaultEnv :: Env
defaultEnv = emptyEnv

newtype Computation a = Computation (Env -> (Env, a))

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

repl :: String -> [String] -> Computation String
repl final [] = pure final
repl str (c : cs) =
  let expr = Either.fromRight (RuntimeError "parseError") (Parsec.parse parseTopExpression "(source)" c)
   in do
        res <- eval expr
        repl (str ++ "\n\n> " ++ c ++ "\n = " ++ show res) cs

computeRes :: Env -> Computation a -> a
computeRes env computation = let (_, res) = compute env computation in res

nativeFn :: (Integer -> Integer -> Integer) -> Expression -> Expression -> Computation Expression
nativeFn fn argA argB = do
  evalA <- eval argA
  evalB <- eval argB
  case (evalA, evalB) of
    (EInteger x, EInteger y) -> return $ EInteger (fn x y)
    _ -> return $ RuntimeError "Don't know how to multiply non-numbers"
    

eval :: Expression -> Computation Expression
eval (Call (Name "+") [xExpr, yExpr]) = nativeFn (+) xExpr yExpr
eval (Call (Name "-") [xExpr, yExpr]) = nativeFn (-) xExpr yExpr
eval (Call (Name "*") [xExpr, yExpr]) = nativeFn (*) xExpr yExpr
eval (Call (Name "/") [xExpr, yExpr]) = nativeFn div xExpr yExpr
eval (Call (Name "%") [xExpr, yExpr]) = nativeFn rem xExpr yExpr
eval (Quote expr) = return expr
eval (Define name expression) = do
  evaluatedExpression <- eval expression
  bind name evaluatedExpression
  return evaluatedExpression
eval (Name x) = readBinding x
eval (Lambda args bodyExpr) = return $ CapturedLambda (evalLambda args bodyExpr)
eval (Call callExpr argExprs) = do
  fn <- eval callExpr
  case fn of
    CapturedLambda fnComputation ->
      let args :: Computation [Expression]
          args =
            foldM
              ( \acc argExpr -> do
                  arg <- eval argExpr
                  return (arg : acc)
              )
              []
              argExprs
       in args >>= fnComputation
    _ ->
      pure (RuntimeError ("I don't know how to call: " ++ show fn))
eval expr = return expr

evalLambda :: [String] -> Expression -> [Expression] -> Computation Expression
evalLambda [] body [] = eval body
evalLambda [] _ _ = return $ RuntimeError "Too many arguments"
evalLambda _ _ [] = return $ RuntimeError "Not enough arguments"
evalLambda (n : ns) body (a : as) = do
  bind n a
  evalLambda ns body as

main :: IO ()
main =
  let test_cases =
        [ "2",
          "(+ 2 1)",
          "(define name \"olivia\")",
          "name",
          "(define x 5)",
          "x",
          "(+ x 1)",
          "(define y (+ x 2))",
          "y",
          "(+ x y)",
          "(lambda (arg) (* arg arg))",
          "((lambda (arg) (* arg arg)) 5)",
          "(define square (lambda (arg) (* arg arg)))",
          "(square x)",
          "(square z)",
          "(quote (square x))",
          "(square (quote x))"
        ]

      evaluations :: Computation String
      evaluations = repl "Starting autoevaluation...\n" test_cases

      finalRes :: String
      finalRes = computeRes defaultEnv evaluations
   in do
        putStrLn ""
        -- putStr (concatMap (\(expr, res) -> "> " ++ expr ++ "\n\t" ++ show res ++ "\n\n") parsedExpressions)
        putStrLn finalRes
        putStrLn "done"
