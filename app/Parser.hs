{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Parser (Token(..), Expression(..), Computation(..), Env(..), parseExpression, parseTopExpression) where

import Control.Applicative
import Control.Monad (foldM, foldM_, liftM)
import qualified Data.Either as Either
import Data.Function
import qualified Data.Map as Map
import Debug.Trace
import System.IO
import qualified Text.Parsec as Parsec

debugPipe :: (Show b) => String -> b -> b
debugPipe name x = trace (name ++ ": " ++ show x) x

data Token
  = EInteger Integer
  | EString String
  | EBool Bool
  | Name String
  | List [Token]
  | Lambda [String] Token
  | Let [(String, Token)] Token
  | CapturedLambda Env ([Token] -> Computation Token)
  | Quote Token
  | IfElse Token Token Token
  | Define String Token
  | DefineType String Token
  | Call Token [Token]
  | ParseError String

data Expression
  = Okay Token
  | RuntimeError2 String
  deriving (Show)

data Env = Env (Map.Map String (Token, Token)) (Maybe Env)

newtype Computation a = Computation (Env -> (Env, a))

instance Show Token where
  show (EInteger x) = show x
  show (EString s) = "\"" ++ s ++ "\""
  show (EBool b) = show b
  show (Name s) = s
  show (List elems) = "(list " ++ (elems & map show & unwords) ++ ")"
  show (Lambda args body) = "(\\" ++ unwords args ++ " -> " ++ show body ++ ")"
  show (CapturedLambda _ _) = "<captured lambda>"
  show (Quote expr) = "(quote " ++ show expr ++ ")"
  show (IfElse cond trueExpr falseExpr) = "(if " ++ show cond ++ " " ++ show trueExpr ++ " " ++ show falseExpr ++ ")"
  show (Define name expr) = "(define " ++ name ++ " " ++ show expr ++ ")"
  show (Call fn args) = "(" ++ show fn ++ " " ++ (args & map show & unwords) ++ ")"
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
      <|> Parsec.string "="
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

