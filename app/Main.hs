module Main where

-- I import qualified so that it's clear which
-- functions are from the parsec library:
import qualified Text.Parsec as Parsec
import Debug.Trace
import Data.List
import Data.Function

-- I am the error message infix operator, used later:
import Text.Parsec ((<?>))

-- Imported so we can play with applicative things later.
-- not qualified as mostly infix operators we'll be using.
import Control.Applicative


-- alias Parsec.parse for more concise usage in my examples:
-- parse rule text = Parsec.parse rule "(source)" text

data Expression =
    Integer Integer |
    Name String |
    Quote Expression |
    Define String Expression |
    DefineType String Expression |
    Call Expression ([Expression]) | 
    Expression ([Expression]) 
    deriving (Eq, Ord, Show)

parseName :: Parsec.Parsec String () Expression
parseName = do 
    name_str <- (Parsec.string "+") <|> Parsec.many1 Parsec.letter
    return (Name name_str)

parseInt :: Parsec.Parsec String () Expression
parseInt = do 
    integer_str <- Parsec.many1 Parsec.digit
    return (Integer (read integer_str))

parseCall :: Parsec.Parsec String () Expression
parseCall = do
    openCall
    name <- parseExpression 
    arguments <- Parsec.many ( do
        separator
        expression <- parseExpression
        return expression)
    closeCall
    return (Call name arguments)

closeCall = do
    Parsec.spaces
    Parsec.char ')'

openCall = do
    Parsec.char '('
    Parsec.spaces

separator = Parsec.many1 Parsec.space

charToString :: Char -> String
charToString c = [c]

parseDefineType :: Parsec.Parsec String () Expression
parseDefineType = do
    openCall
    Parsec.string "defineType"
    separator
    name <- Parsec.many1 Parsec.letter
    separator
    value <- parseExpression
    closeCall
    return (DefineType name value)

parseDefine :: Parsec.Parsec String () Expression
parseDefine = do
    openCall
    Parsec.string "define"
    separator
    name <- Parsec.many1 Parsec.letter
    separator
    value <- parseExpression
    closeCall
    return (Define name value)

parseQuote :: Parsec.Parsec String () Expression
parseQuote = do
    openCall
    Parsec.string "quote"
    separator
    expression <- parseExpression
    closeCall
    return (Quote expression)

parseExpression :: Parsec.Parsec String () Expression
parseExpression =
    parseInt
    <|> parseName
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
    let
        test_cases =
            [ "5",
              "+ 5",
              "name",
              "(+ 2 3)",
              "(define x 5)",
              "(define x (squared 5))",
              "(quote y)"
              ]

        parsed :: [(String, Either Parsec.ParseError Expression)]
        parsed = map
            (\expr -> (expr, (Parsec.parse parseTopExpression "(source)" expr )))
            test_cases
    in do
        putStrLn ""
        putStr (parsed & map (\(expr, res) -> "> " ++ expr ++ "\n\t" ++ show res ++ "\n\n") & concat)
        putStrLn "done"
