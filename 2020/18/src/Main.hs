module Main (main) where

import Data.Maybe (fromJust)

import qualified Au.Parser as Au
import Au.Parser hiding (Parser)

type Parser = Au.Parser Char

term :: Parser Int
term = (integer <> parenthesised term) `chainl1` keywords [" + " .= (+), " * " .= (*)]

main :: IO ()
main = do
  input <- readFile "input"
  print . sum . fromJust . parse (perLine term) $ input
