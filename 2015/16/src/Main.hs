module Main (main) where

import Data.Map.Strict (Map, fromList, keys, (!))

import Au.Parser hiding (matches)

type Sue = Map String Integer
type Sues = [(Integer, Sue)]
type Matcher = Sue -> Sue -> Bool
type Comparator = String -> Integer -> Integer -> Bool

sues :: Tokenizer Sues
sues = perLine sue

sue :: Tokenizer (Integer, Sue)
sue = (,)
  <$> (word "Sue " >> integer)
  <*> (word ": " >> (fromList <$> separatedBy (word ", ") compound))

compound :: Tokenizer (String, Integer)
compound = (,) <$> alphabetical <*> (word ": " >> integer)

targetSue :: Tokenizer Sue
targetSue = fromList <$> perLine compound

matches :: Comparator -> Matcher
matches c target sue' = and
  [ c k (sue' ! k) (target ! k)
  | k <- keys sue'
  ]

solve :: (Sue -> Bool) -> Sues -> Integer
solve matches' = fst . head . filter (matches' . snd)

comparePart2 :: Comparator
comparePart2 = \case
  "cats" -> (>)
  "trees" -> (>)
  "pomeranians" -> (<)
  "goldfish" -> (<)
  _ -> (==)

main :: IO ()
main = do
  Just possibleSues <- parse sues <$> readFile "input"
  Just target <- parse targetSue <$> readFile "target"
  print . solve (matches (const (==)) target) $ possibleSues
  print . solve (matches comparePart2 target) $ possibleSues
