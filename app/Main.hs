{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
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

data Token
  = EInteger Integer
  | EString String
  | Name String
  | Lambda [String] Token
  | Let [(String, Token)] Token
  | CapturedLambda ([Token] -> Computation Token)
  | Quote Token
  | IfElse Token Token Token
  | Define String Token
  | DefineType String Token
  | Call Token [Token]
  | ParseError String

data Expression
  = Okay Token
  | RuntimeError2 String

instance Show Token where
  show (EInteger x) = show x
  show (EString s) = "\"" ++ s ++ "\""
  show (Name s) = s
  show (Lambda args body) = "(lambda (" ++ (map show args & unwords) ++ ") " ++ show body ++ ")"
  show (CapturedLambda _) = "<captured lambda>"
  show (Quote expr) = "(quote " ++ show expr ++ ")"
  show (Define name expr) = "(define " ++ name ++ " " ++ show expr ++ ")"
  show (Call fn args) = "call(" ++ show fn ++ " " ++ (args & map show & unwords) ++ ")"
  show (ParseError err) = "Error: " ++ err
  show _ = "unknown expression"

parseName :: Parsec.Parsec String () Token
parseName = do
  name_str <-
    Parsec.string "+"
      <|> Parsec.string "*"
      <|> Parsec.string "/"
      <|> Parsec.string "-"
      <|> Parsec.string "%"
      <|> parseNamestring
  return (Name name_str)

parseString :: Parsec.Parsec String () Token
parseString = do
  _ <- Parsec.char '"'
  str <- Parsec.manyTill Parsec.anyChar (Parsec.char '"')
  return (EString str)

parseInt :: Parsec.Parsec String () Token
parseInt = do
  integer_str <- Parsec.many1 Parsec.digit
  return (EInteger (read integer_str))

inParens :: Parsec.Parsec String () a -> Parsec.Parsec String () a
inParens parser = do
  openCall
  res <- parser
  closeCall
  return res

parseCall :: Parsec.Parsec String () Token
parseCall =
  inParens $ do
    name <- parseExpression
    arguments <-
      Parsec.many
        ( do
            separator
            parseExpression
        )
    return (Call name arguments)

parseLambda :: Parsec.Parsec String () Token
parseLambda = do
  inParens $
    do
      parseKeyword "lambda"
      separator
      args <- inParens $ do
        parseNamestring `Parsec.sepBy` separator
      separator
      Lambda args <$> parseExpression

parseTuple :: Parsec.Parsec String () (String, Token)
parseTuple =
  inParens $ do
    name <- parseNamestring
    separator
    value <- parseExpression
    return (name, value)

parseLet :: Parsec.Parsec String () Token
parseLet = do
  inParens $ do
    parseKeyword "let"
    separator
    bindings <- inParens $ do parseTuple `Parsec.sepBy` separator

    separator
    body <- parseExpression
    return (Let bindings body)

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

parseNamestring :: Parsec.Parsec String () String
parseNamestring = do
  Parsec.many1 Parsec.letter

separator :: Parsec.Parsec String () ()
separator = do
  _ <- Parsec.many1 Parsec.space
  return ()

parseDefineType :: Parsec.Parsec String () Token
parseDefineType =
  inParens $ do
    parseKeyword "defineType"
    separator
    name <- parseNamestring
    separator
    value <- parseExpression
    return (DefineType name value)

parseIfElse :: Parsec.Parsec String () Token
parseIfElse =
  inParens $ do
    parseKeyword "if"
    separator
    condExpr <- parseExpression
    separator
    trueExpr <- parseExpression
    separator
    falseExpr <- parseExpression
    return (IfElse condExpr trueExpr falseExpr)

parseDefine :: Parsec.Parsec String () Token
parseDefine =
  inParens $ do
    parseKeyword "define"
    separator
    name <- parseNamestring
    separator
    value <- parseExpression
    return (Define name value)

parseQuote :: Parsec.Parsec String () Token
parseQuote = do
  inParens $ do
    _ <- Parsec.string "quote"
    separator
    expression <- parseExpression
    return (Quote expression)

parseExpression :: Parsec.Parsec String () Token
parseExpression =
  parseInt
    <|> parseString
    <|> parseName
    <|> Parsec.try parseLet
    <|> Parsec.try parseLambda
    <|> Parsec.try parseDefine
    <|> Parsec.try parseDefineType
    <|> Parsec.try parseQuote
    <|> Parsec.try parseIfElse
    <|> parseCall

parseTopExpression :: Parsec.Parsec String () Token
parseTopExpression = do
  expr <- parseExpression
  Parsec.eof
  return expr

--------------------------------
-- Evaluation

data Env = Env (Map.Map String Token) (Maybe Env)

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

bind :: String -> Token -> Computation ()
bind name expression =
  Computation
    ( \(Env mappings parentEnv) ->
        (Env (mappings & Map.insert name expression) parentEnv, ())
    )

readBinding :: String -> Computation Token
readBinding name =
  Computation
    ( \env@(Env mappings parent) ->
        let lookupRes = Map.lookup name mappings
         in case (lookupRes, parent) of
              (Just value, _) -> (env, value)
              (Nothing, Just parentEnv) -> compute parentEnv (readBinding name)
              (Nothing, Nothing) -> (env, ParseError ("name '" ++ name ++ "' not found"))
    )

-- | The default environment is not the empty environment!
defaultEnv :: Env
defaultEnv = emptyEnv

repl :: String -> [String] -> Computation String
repl final [] = pure final
repl str (c : cs) =
  let expr =
        c
          & Parsec.parse parseTopExpression "(source)"
          & Either.either (\err -> err & show & ParseError) id
   in do
        res <- eval expr
        repl (str ++ "\n\n> " ++ c ++ "\n = " ++ show res) cs

nativeFn :: (Integer -> Integer -> Integer) -> Token -> Token -> Computation Token
nativeFn fn argA argB = do
  evalA <- eval argA
  evalB <- eval argB
  case (evalA, evalB) of
    (EInteger x, EInteger y) -> return $ EInteger (fn x y)
    _ -> return $ ParseError "Don't know how to multiply non-numbers"

eval :: Token -> Computation Token
eval (Call (Name "+") [xExpr, yExpr]) = nativeFn (+) xExpr yExpr
eval (Call (Name "-") [xExpr, yExpr]) = nativeFn (-) xExpr yExpr
eval (Call (Name "*") [xExpr, yExpr]) = nativeFn (*) xExpr yExpr
eval (Call (Name "/") [xExpr, yExpr]) = nativeFn div xExpr yExpr
eval (Call (Name "%") [xExpr, yExpr]) = nativeFn rem xExpr yExpr
eval (Quote expr) = return expr
eval (Call (Name "eval") [Quote expr]) = eval expr
eval (Let bindings expression) = do
  inChildEnv
    ( do
        foldM_ (\_ (name, value) -> do bind name value) () bindings
        eval expression
    )
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
      let args :: Computation [Token]
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
      pure (ParseError ("I don't know how to call: " ++ show fn))
eval expr = return expr

evalLambda :: [String] -> Token -> [Token] -> Computation Token
evalLambda [] body [] = do eval body
evalLambda [] _ _ = return $ ParseError "Too many arguments"
evalLambda _ _ [] = return $ ParseError "Not enough arguments"
evalLambda (n : ns) body (a : as) = do
  inChildEnv
    ( do
        -- we currently eagerly evaluate
        -- evalA <- eval a
        bind n a
        evalLambda ns body as
    )

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
          "(square x y)",
          "(square x)",
          "(square z)",
          "(quote (square x))",
          "(square (quote x))",
          "(eval (quote (square x)))",
          "((eval (quote square)) x)",
          "\"done\""
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
