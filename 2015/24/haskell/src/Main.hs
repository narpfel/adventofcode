module Main (main) where

import Data.List (subsequences)
import Data.Word (Word64)

weight :: Num a => [a] -> a
weight = sum

quantumEntanglement :: Num a => [a] -> a
quantumEntanglement = product

solve :: Word64 -> [Word64] -> Word64
solve targetWeight
  = minimum
  . map quantumEntanglement
  . filter ((== targetWeight) . weight)
  . subsequences

main :: IO ()
main = do
  input <- map read . lines <$> readFile "input"
  let part1 = weight input `div` 3
      part2 = weight input `div` 4
  print . solve part1 $ input
  print . solve part2 $ input
