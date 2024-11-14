{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Parser (Expression (..), Env (..), parseExpression, parseTopExpression) where

import Control.Applicative
import Data.Function
import qualified Data.Map as Map
import Debug.Trace
import qualified Text.Parsec as Parsec

debugPipe :: (Show b) => String -> b -> b
debugPipe name x = trace (name ++ ": " ++ show x) x

data Expression
  = EInteger Integer
  | EString String
  | EBool Bool
  | Name String
  | List [Expression]
  | Lambda [String] Expression
  | Let [(String, Expression)] Expression
  | CapturedLambda Env [String] Expression
  | Quote Expression
  | IfElse Expression Expression Expression
  | Define String Expression
  | DefineType String Expression
  | Call Expression [Expression]
  deriving (Eq)

-- deriving (Show)

data Env = Env (Map.Map String (Expression, Expression)) (Maybe Env) deriving (Show, Eq)

instance Show Expression where
  show (EInteger x) = show x
  show (EString s) = "\"" ++ s ++ "\""
  show (EBool b) = show b
  show (Name s) = s
  show (List elems) = "(list " ++ (elems & map show & unwords) ++ ")"
  show (Lambda args body) = "(\\" ++ unwords args ++ " -> " ++ show body ++ ")"
  show (Let argValues body) = "(let\n    " ++ (argValues & map (\(n, v) -> "  (" ++ n ++ " = " ++ show v ++ ")") & unwords) ++ "\n     " ++ show body ++ ")"
  -- show (CapturedLambda _ _) = "<captured lambda>"
  show (Quote expr) = "(quote " ++ show expr ++ ")"
  show (IfElse cond trueExpr falseExpr) = "(if " ++ show cond ++ " " ++ show trueExpr ++ " " ++ show falseExpr ++ ")"
  show (Define name expr) = "(define " ++ name ++ " " ++ show expr ++ ")"
  show (Call fn args) = "(" ++ show fn ++ " " ++ (args & map show & unwords) ++ ")"
  show (CapturedLambda env argNames body) = "<Captured Lambda: " ++ show (Lambda argNames body) ++ " in env:\n  " ++ show env ++ "\n  >"
  show _ = "(don't know how to display this expression)"

parseName :: Parsec.Parsec String () Expression
parseName = do
  name_str <-
    Parsec.string "+"
      <|> Parsec.string "*"
      <|> Parsec.string "/"
      <|> Parsec.string "-"
      <|> Parsec.string "%"
      <|> Parsec.string "="
      <|> parseNamestring
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

inParens :: Parsec.Parsec String () a -> Parsec.Parsec String () a
inParens parser = do
  openCall
  res <- parser
  closeCall
  return res

parseCall :: Parsec.Parsec String () Expression
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

parseList :: Parsec.Parsec String () Expression
parseList =
  inParens $
    do
      parseKeyword "list"
      elems <-
        Parsec.many
          ( do
              separator
              parseExpression
          )
      return (List elems)

parseLambda :: Parsec.Parsec String () Expression
parseLambda = do
  inParens $
    do
      parseKeyword "lambda"
      separator
      args <- inParens $ do
        parseNamestring `Parsec.sepBy` separator
      separator
      Lambda args <$> parseExpression

parseTuple :: Parsec.Parsec String () (String, Expression)
parseTuple =
  inParens $ do
    name <- parseNamestring
    separator
    value <- parseExpression
    return (name, value)

parseLet :: Parsec.Parsec String () Expression
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

parseDefineType :: Parsec.Parsec String () Expression
parseDefineType =
  inParens $ do
    parseKeyword "defineType"
    separator
    name <- parseNamestring
    separator
    value <- parseExpression
    return (DefineType name value)

parseIfElse :: Parsec.Parsec String () Expression
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

parseDefine :: Parsec.Parsec String () Expression
parseDefine =
  inParens $ do
    parseKeyword "define"
    separator
    name <- parseNamestring
    separator
    value <- parseExpression
    return (Define name value)

parseQuote :: Parsec.Parsec String () Expression
parseQuote = do
  inParens $ do
    _ <- Parsec.string "quote"
    separator
    expression <- parseExpression
    return (Quote expression)

parseExpression :: Parsec.Parsec String () Expression
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
    <|> Parsec.try parseList
    <|> parseCall

parseTopExpression :: Parsec.Parsec String () Expression
parseTopExpression = do
  expr <- parseExpression
  Parsec.eof
  return expr
