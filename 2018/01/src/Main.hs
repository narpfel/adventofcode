module Main where

import Data.Foldable (asum)
import qualified Data.IntSet as IntSet
import Data.List (unfoldr)
import Data.Maybe (fromJust)

partialSums :: Num a => [a] -> [a]
partialSums xs = unfoldr (uncurry f) (xs, 0)
  where
    f (x:xs) s = Just (x + s, (xs, x + s))
    f [] _ = Nothing

part2 :: [Int] -> Maybe Int
part2 input = asum $ unfoldr (uncurry f) (input, mempty)
  where
    f (x:xs) set = Just (if x `IntSet.member` set then Just x else Nothing, (xs, IntSet.insert x set))
    f [] _ = Nothing

main :: IO ()
main = do
  input <- map read . lines . filter (/= '+') <$> readFile "input" :: IO [Int]
  print . sum $ input
  print . fromJust . part2 . partialSums . cycle $ input
