module Main where

import Au.Parser
import Control.Applicative (some)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type Patterns = Map [Bool] Bool

input :: Parser Char (IntSet, Patterns)
input
  = (,)
  <$> (initialState <* newline)
  <*> patterns

initialState :: Parser Char IntSet
initialState = word "initial state: " *> (fromBools <$> some cell) <* newline

cell :: Parser Char Bool
cell
  = anything >>= \case
      '#' -> pure True
      '.' -> pure False
      _ -> mempty

fromBools :: [Bool] -> IntSet
fromBools
  = IntSet.fromAscList
  . fmap fst
  . filter snd
  . zip [0..]

patterns :: Parser Char Patterns
patterns = Map.fromList <$> perLine pattern

pattern :: Parser Char ([Bool], Bool)
pattern
  = (,)
  <$> (some cell <* word " => ")
  <*> cell

window :: Int -> IntSet -> Int -> [Bool]
window len set position = (`IntSet.member` set) <$> [position - len .. position + len]

windows :: Int -> IntSet -> [(Int, [Bool])]
windows len set = zip positions (window len set <$> positions)
  where
    positions = [IntSet.findMin set - len .. IntSet.findMax set + len]

nextGeneration :: Patterns -> IntSet -> IntSet
nextGeneration pats
  = IntSet.fromAscList
  . fmap fst
  . filter ((pats Map.!) . snd)
  . windows 2

part1 :: Patterns -> Int -> IntSet -> Int
part1 patterns' generationCount
  = sum
  . IntSet.toAscList
  . (!! generationCount)
  . iterate (nextGeneration patterns')

printInfosForGeneration :: Int -> IO ()
printInfosForGeneration n = do
  Just (state, patterns') <- parse input <$> readFile "input"
  putStrLn ""
  print n
  let finalGeneration = (!! n) . iterate (nextGeneration patterns') $ state
  print . sum . IntSet.toAscList $ finalGeneration
  let min' = IntSet.findMin finalGeneration
      max' = IntSet.findMax finalGeneration
  print min'
  print max'
  print $ max' - min'
  putStrLn ""

-- This was found by examining the range of pots with plants for generations
-- 500, 5_000 and 50_000. The solution for 50_000_000_000 is extrapolated from there.
part2 :: Integer -> Patterns -> IntSet -> Integer
part2 n patterns' state = (n - 500) * increasePerGeneration + x
  where
    x = fromIntegral $ part1 patterns' 500 state
    y = fromIntegral $ part1 patterns' 5_000 state
    increasePerGeneration = fromIntegral $ (y - x) `div` 4_500

main :: IO ()
main = do
  Just (state, patterns') <- parse input <$> readFile "input"
  print . part1 patterns' 20 $ state
  -- Not even close to fast enough.
  -- print . part1 patterns' 1_000_000 $ state
  print . part2 50_000_000_000 patterns' $ state
