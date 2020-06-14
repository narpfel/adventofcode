module Main where

import Data.List (foldl')

dotProduct :: Num a => [a] -> [a] -> a
dotProduct xs = foldl' (+) 0 . zipWith (*) xs

lastDigit :: Integral a => a -> a
lastDigit = abs . (`rem` 10)

fromDecimalDigits :: Num a => [a] -> a
fromDecimalDigits = foldl' (\acc x -> acc * 10 + x) 0

fftPart1 :: [Int] -> [Int]
fftPart1 xs
  = map (lastDigit . dotProduct xs . pattern) indices
  where
    basePattern = [0, 1, 0, -1]
    pattern n
      = tail
      . cycle
      . concatMap (replicate n)
      $ basePattern
    indices = zipWith (curry fst) [1..] xs

fftPart2 :: [Int] -> [Int]
fftPart2 = map lastDigit . scanr1 (+)

solve :: Int -> ([Int] -> [Int]) -> [Int] -> Int
solve offset fft
  = fromDecimalDigits
  . take 8
  . (!! 100)
  . iterate fft
  . drop offset

part1 :: [Int] -> Int
part1 = solve 0 fftPart1

part2 :: [Int] -> Int
part2 input
  = solve offset fftPart2
  . concat
  . replicate 10_000
  $ input
  where
    offset = fromDecimalDigits . take 7 $ input

main :: IO ()
main = do
  input <- map (read . pure) . init <$> readFile "input"
  print . part1 $ input
  print . part2 $ input
