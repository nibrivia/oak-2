module Main where

-- I import qualified so that it's clear which
-- functions are from the parsec library:

-- I am the error message infix operator, used later:

-- Imported so we can play with applicative things later.
-- not qualified as mostly infix operators we'll be using.
import Control.Applicative
import Data.Function
import Data.List
import Debug.Trace
import Text.Parsec ((<?>))
import qualified Text.Parsec as Parsec

-- alias Parsec.parse for more concise usage in my examples:
-- parse rule text = Parsec.parse rule "(source)" text

data Expression
  = EInteger Integer
  | EString String
  | Name String
  | Lambda [Expression] Expression
  | Quote Expression
  | IfElse Expression Expression Expression
  | Define String Expression
  | DefineType String Expression
  | Call Expression [Expression]
  | Expression [Expression]
  deriving (Eq, Ord, Show)

parseName :: Parsec.Parsec String () Expression
parseName = do
  name_str <-
    Parsec.string "+"
      <|> Parsec.string "*"
      <|> Parsec.string "/"
      <|> Parsec.string "-"
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
  args <- parseExpression `Parsec.sepBy` separator
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

charToString :: Char -> String
charToString c = [c]

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
    <|> parseCall

parseTopExpression :: Parsec.Parsec String () Expression
parseTopExpression = do
  expr <- parseExpression
  Parsec.eof
  return expr

main :: IO ()
main =
  let test_cases =
        [ "5",
          "(+ 2 3)",
          "(define name \"olivia\")",
          "name",
          "(define x 5)",
          "(lambda (arg) (* arg arg))",
          "(define square (lambda (arg) (* arg arg)))",
          "(square 5)",
          "(quote (square x))",
          "(square (quote x))"
        ]

      parsed :: [(String, Either Parsec.ParseError Expression)]
      parsed =
        map
          (\expr -> (expr, Parsec.parse parseTopExpression "(source)" expr))
          test_cases
   in do
        putStrLn ""
        putStr (concatMap (\(expr, res) -> "> " ++ expr ++ "\n\t" ++ show res ++ "\n\n") parsed)
        putStrLn "done"
