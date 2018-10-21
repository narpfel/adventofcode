module Main where

codes :: [Integer]
codes = iterate ((`rem` 33554393) . (* 252533)) 20151125

coord2index :: Int -> Int -> Int
coord2index column row = column + gauß (row + column - 2)

gauß :: Int -> Int
gauß n = n * (n + 1) `div` 2

inputColumn :: Int
inputColumn = 3019

inputRow :: Int
inputRow = 3010

main :: IO ()
main = do
  print $ codes !! (coord2index inputColumn inputRow - 1)
