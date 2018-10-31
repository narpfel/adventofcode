module Main where

import Data.List (subsequences)

weight :: Num a => [a] -> a
weight = sum

quantumEntanglement :: Num a => [a] -> a
quantumEntanglement = product

solve :: Integer -> [Integer] -> Integer
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
