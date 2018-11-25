module Main where

import Control.Applicative (some)
import Data.Char (isSpace)
import Data.Functor (($>))
import Data.Maybe (fromJust)

import Au.Parser

decompress :: Parser Char Integer
decompress = sum <$> (some $ choice [decompressMarker, anything $> 1])

decompressMarker :: Parser Char Integer
decompressMarker = do
  word "("
  length' <- integer
  word "x"
  repeat' <- integer
  word ")"
  exactly length' anything
  pure $ length' * repeat'

main :: IO ()
main = do
  input <- filter (not . isSpace) <$> readFile "input"
  print . fromJust . parse decompress $ input
