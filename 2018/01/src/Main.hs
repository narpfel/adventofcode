module Main (main) where

import Data.Foldable (asum)
import qualified Data.IntSet as IntSet
import Data.List (scanl', mapAccumL)
import Data.Maybe (fromJust)

partialSums :: Num a => [a] -> [a]
partialSums = scanl' (+) 0

part2 :: [Int] -> Maybe Int
part2 = asum . snd . mapAccumL f mempty . partialSums . cycle
  where
    f set x = (IntSet.insert x set, if x `IntSet.member` set then Just x else Nothing)

main :: IO ()
main = do
  input <- map read . lines . filter (/= '+') <$> readFile "input" :: IO [Int]
  print . sum $ input
  print . fromJust . part2 $ input
