module Main where

import Data.List (scanl')
import Data.List.Split (splitOn)

data Direction
  = North
  | NorthEast
  | SouthEast
  | South
  | SouthWest
  | NorthWest

parse :: String -> Direction
parse "n" = North
parse "ne" = NorthEast
parse "se" = SouthEast
parse "s" = South
parse "sw" = SouthWest
parse "nw" = NorthWest
parse s = error $ "Parse invalid Direction string " ++ show s

data Position = Position Int Int deriving Show

move :: Position -> Direction -> Position
move (Position x y) North
  = Position x (y + 1)
move (Position x y) NorthEast
  | even x = Position (x + 1) y
  | otherwise = Position (x + 1) (y + 1)
move (Position x y) SouthEast
  | even x = Position (x + 1) (y - 1)
  | otherwise = Position (x + 1) y
move (Position x y) South
  = Position x (y - 1)
move (Position x y) SouthWest
  | even x = Position (x - 1) (y - 1)
  | otherwise = Position (x - 1) y
move (Position x y) NorthWest
  | even x = Position (x - 1) y
  | otherwise = Position (x - 1) (y + 1)

distance :: Position -> Int
distance (Position 0 y) = abs y
distance (Position x 0) = abs x
distance p@(Position x y)
  | x < 0 = distance (Position (-x) y)
  | y < 0 && even x = distance (Position x (-y))
  | y < 0 && odd x = distance (Position x (-y - 1))
  | otherwise = 1 + (distance $ move p SouthWest)

main :: IO ()
main = do
  directions <- map parse . splitOn "," . head . lines <$> readFile "input"
  let distances = map distance . scanl' move (Position 0 0) $ directions
  print . last $ distances
  print . maximum $ distances
