module Main (main) where

import Data.Maybe (fromJust)

import qualified Au.Parser as Au
import Au.Parser hiding (Parser)

type Parser = Au.Parser Char

samePrecedenceTerm :: Parser Integer
samePrecedenceTerm =
  (integer <> parenthesised samePrecedenceTerm)
    `chainl1` keywords [" + " .= (+), " * " .= (*)]

tightAdditionTerm :: Parser Integer
tightAdditionTerm = factor `chainl1` keywords [" * " .= (*)]

factor :: Parser Integer
factor = (integer <> parenthesised tightAdditionTerm) `chainl1` keywords [" + " .= (+)]

solve :: Parser Integer -> String -> Integer
solve term = sum . fromJust . parse (perLine term)

main :: IO ()
main = do
  input <- readFile "input"
  print . solve samePrecedenceTerm $ input
  print . solve tightAdditionTerm $ input
