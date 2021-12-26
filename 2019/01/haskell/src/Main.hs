module Main (main) where

fuelRequirement :: Int -> Int
fuelRequirement x
  | x < 0 = 0
  | otherwise = (x `div` 3) - 2

part1 :: [Int] -> Int
part1 = sum . map fuelRequirement

part2 :: [Int] -> Int
part2 = sum . concatMap (takeWhile (> 0) . drop 1 . iterate fuelRequirement)

main :: IO ()
main = do
  input <- map read . lines <$> readFile "input"
  print . part1 $ input
  print . part2 $ input
