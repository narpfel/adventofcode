module Main (main) where

import Data.Foldable (maximumBy)
import Data.List (scanl', transpose)
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
  = [ (x, y, windowSize, c + a - d - b)
    | x <- [1..cols m - windowSize - 1]
    , y <- [1..rows m - windowSize - 1]
    , let a = m `atIndex` (y, x)
          b = m `atIndex` (y, x + windowSize)
          c = m `atIndex` (y + windowSize, x + windowSize)
          d = m `atIndex` (y + windowSize, x)
    ]

prefixSum :: Matrix I -> Matrix I
prefixSum = fromLists . map (scanl' (+) 0) . transpose . map (scanl' (+) 0) . toLists

solve :: Matrix I -> [Int] -> (Int, Int, Int, I)
solve prefixSummedPowerLevels
  = maximumBy (comparing (\(_, _, _, d) -> d))
  . concatMap (windowed prefixSummedPowerLevels)

main :: IO ()
main = do
  let prefixSummedPowerLevels = prefixSum . powerLevel $ input
  let (x, y, _, _) = solve prefixSummedPowerLevels [3]
  putStrLn $ show x <> "," <> show y
  let (x', y', windowSize, _) = solve prefixSummedPowerLevels [1..gridSize]
  putStrLn $ show x' <> "," <> show y' <> "," <> show windowSize
