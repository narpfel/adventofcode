module Main where

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = powerset xs ++ map (x:) (powerset xs)

weight :: Num a => [a] -> a
weight = sum

quantumEntanglement :: Num a => [a] -> a
quantumEntanglement = product

solve :: Int -> [Int] -> Int
solve targetWeight
  = minimum
  . filter (>= 0)
  . map quantumEntanglement
  . filter ((== targetWeight) . weight)
  . powerset

main :: IO ()
main = do
  input <- map read . lines <$> readFile "input"
  let part1 = weight input `div` 3
      part2 = weight input `div` 4
  print . solve part1 $ input
  print . solve part2 $ input
