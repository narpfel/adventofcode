{-# OPTIONS_GHC -Wall -Wextra -O2 #-}
{-# LANGUAGE ParallelListComp, Strict #-}

module Main where

import Data.Bool (bool)
import Data.List (transpose)

type Universe = [[Bool]]

showUniverse :: Universe -> String
showUniverse = unlines . (map . map) (bool '.' '#')

readBool :: Char -> Maybe Bool
readBool '.' = Just False
readBool '#' = Just True
readBool _ = Nothing

readUniverse :: [String] -> Maybe Universe
readUniverse = (mapM . mapM) readBool

toIntMatrix :: Universe -> [[Int]]
toIntMatrix = (map . map) fromEnum

shift :: Int -> [Bool] -> [Bool]
shift n xs
  | n >= 0 =
    let (l, r) = splitAt n xs
    in r ++ replicate (min n (length l)) False
  | otherwise =
    let (l, r) = splitAt (length xs + n) xs
    in replicate (min (-n) (length r)) False ++ l

shiftEach :: Int -> Universe -> Universe
shiftEach n = transpose . map (shift n) . transpose

shifts :: Universe -> [Universe]
shifts universe =
  [ f . map g $ universe
  | f <- map shiftEach [-1 .. 1]
  , g <- map shift [-1 .. 1]
  ]

countLights :: Universe -> Int
countLights = sum . map sum . toIntMatrix

life :: Universe -> Universe
life universe =
  [ [n == 3 || (n == 4 && c) | c <- row | n <- neighboursRow]
  | row <- universe
  | neighboursRow <- neighbours
  ]
  where
    neighbours =
      (map . map) sum . map transpose . transpose . map toIntMatrix . shifts $ universe

modifiedLife :: Universe -> Universe
modifiedLife universe =
  [ [ light ||
    (x `elem` [0, length (head universe) - 1] && (y `elem` [0, length universe - 1]))
    | (x, light) <- zip [0 ..] row
    ]
  | (y, row) <- zip [0 ..] (life universe)
  ]

main :: IO ()
main = do
  Just universe <- readUniverse . lines <$> readFile "input"
  print . countLights $ iterate life universe !! 100
  print . countLights $ iterate modifiedLife universe !! 100
