module Main (main) where

import Control.Applicative (many, some)
import Data.List (sort)
import Data.List.Split (splitOn)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Semigroup (Max(..))

import Au.Parser

statement :: Parser Char (Int, [Int])
statement =
  (,)
  <$> (timestamp *> word " Guard #" *> integer <* word " begins shift\n")
  <*> (concat <$> many sleepPeriod)

timestamp :: Parser Char Int
timestamp = read . last . splitOn ":" <$> bracketed (exactly timestampLength anything)
  where
    timestampLength = fromIntegral . length $ "YYYY-MM-DD HH:MM"

sleepPeriod :: Parser Char [Int]
sleepPeriod = do
  startTime <- timestamp <* word " falls asleep\n"
  endTime <- timestamp <* word " wakes up\n"
  pure [startTime .. endTime - 1]

count :: [Int] -> IntMap Int
count = IntMap.unionsWith (+) . map (flip IntMap.singleton 1)

keyOfMaximumBy :: (Bounded a, Ord a) => (b -> a) -> IntMap b -> IntMap.Key
keyOfMaximumBy f = snd . getMax . IntMap.foldMapWithKey (\k v -> Max (f v, k))

solve :: (IntMap Int -> Int) -> IntMap (IntMap Int) -> Int
solve f input = targetGuard * targetMinute
  where
    targetGuard = keyOfMaximumBy f input
    targetMinute = keyOfMaximumBy id $ input IntMap.! targetGuard

part1 :: IntMap (IntMap Int) -> Int
part1 = solve sum

part2 :: IntMap (IntMap Int) -> Int
part2 = solve $ getMax . foldMap Max

main :: IO ()
main = do
  Just input <- parse (some statement) . unlines . sort . lines <$> readFile "input"
  let guard2sleepTimes
        = IntMap.map count
        . IntMap.unionsWith (++)
        . map (uncurry IntMap.singleton)
        $ input
  print . part1 $ guard2sleepTimes
  print . part2 $ guard2sleepTimes
