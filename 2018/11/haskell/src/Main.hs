module Main where

import Data.Foldable (maximumBy)
import Data.Ord (comparing)
import Numeric.LinearAlgebra hiding ((<>))

gridSize :: Int
gridSize = 300

input :: I
input = 7672

powerLevel :: I -> Matrix I
powerLevel serialNumber
  = cmap
    ( (+ negate 5)
    . (`rem` 10)
    . (`div` 100)
    )
  . (* asColumn rackId)
  . cmap (+ serialNumber)
  $ rackId `outer` y
  where
    x = range (gridSize + 1)
    y = range (gridSize + 1)
    rackId = cmap (+ 10) x

windowed :: Matrix I -> Int -> [(Int, Int, Int, I)]
windowed m windowSize
  = [ (x, y, windowSize, sumElements m')
    | x <- [1..cols m - windowSize]
    , y <- [1..rows m - windowSize]
    , let m' = subMatrix (x, y) (windowSize, windowSize) m
    ]

solve :: I -> [Int] -> (Int, Int, Int, I)
solve serialNumber
  = maximumBy (comparing (\(_, _, _, d) -> d))
  . concatMap (windowed $ powerLevel serialNumber)

main :: IO ()
main = do
  let (x, y, _, _) = solve input [3]
  putStrLn $ show x <> "," <> show y
  let (x', y', windowSize, _) = solve input [1..gridSize]
  putStrLn $ show x' <> "," <> show y' <> "," <> show windowSize
