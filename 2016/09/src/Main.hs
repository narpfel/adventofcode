module Main where

import Control.Applicative (some)
import Data.Char (isSpace)
import Data.Maybe (fromJust)

import Au.Parser

decompress :: Parser Char String
decompress = concat <$> (some $ choice [decompressMarker, pure <$> anything])

decompressMarker :: Parser Char String
decompressMarker = do
  word "("
  length' <- integer
  word "x"
  repeat' <- integer
  word ")"
  string <- exactly length' anything
  pure . concat . replicate repeat' $ string

main :: IO ()
main = do
  input <- filter (not . isSpace) <$> readFile "input"
  print . length . fromJust . parse decompress $ input
