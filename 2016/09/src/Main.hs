module Main (main) where

import Control.Applicative (some)
import Data.Char (isSpace)
import Data.Functor (($>))
import Data.Maybe (fromJust)

import Au.Parser

data Recursiveness = Flat | DecompressInner

decompress :: Recursiveness -> Parser Char Integer
decompress recursiveness =
  sum <$> some (choice [decompressMarker recursiveness, anything $> 1])

decompressMarker :: Recursiveness -> Parser Char Integer
decompressMarker recursiveness = do
  word "("
  length' <- integer
  word "x"
  repeat' <- integer
  word ")"
  string <- exactly length' anything
  let Just innerLength = parse (decompress recursiveness) string
  pure $ repeat' * case recursiveness of
                     Flat -> length'
                     DecompressInner -> innerLength

main :: IO ()
main = do
  input <- filter (not . isSpace) <$> readFile "input"
  print . fromJust . parse (decompress Flat) $ input
  print . fromJust . parse (decompress DecompressInner) $ input
