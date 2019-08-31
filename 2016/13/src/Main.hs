module Main where

import Data.Bits (popCount)
import Data.List.Extra (nubOrdOn)

data Point = Point
  { x :: Int
  , y :: Int
  , distance :: Int
  } deriving (Show, Eq, Ord)

(.+) :: Point -> Point -> Point
(Point x y d) .+ (Point x' y' d') = Point (x + x') (y + y') (d + d')

neightbours :: Point -> [Point]
neightbours p =
  (.+ p) . (\(x, y) -> Point x y 1)
  <$> [ (-1, 0)
      , (0, -1)
      , (1, 0)
      , (0, 1)]

isValid :: Point -> Bool
isValid Point {..} = x >= 0 && y >= 0

isOpen :: Point -> Bool
isOpen Point {..} =
  even . popCount $ (input + x * x + 3 * x + 2 * x * y + y + y * y)

startPoint :: Point
startPoint = Point 1 1 0

allPoints :: [Point]
allPoints =
  startPoint
  : ( filter isOpenAndValid
    . nubOrdOn (\Point {..} -> (x, y))
    . concatMap neightbours
    $ allPoints
    )
  where
    isOpenAndValid
      = and
      . sequence
        [ isOpen
        , isValid
        -- filter extraneous startPoint that nubOrdOn doesn’t catch
        , \Point {..} -> x /= 1 || y /= 1
        ]

part1 :: Int
part1
  = distance
  . head
  . filter (\Point {..} -> x == 31 && y == 39)
  $ allPoints

part2 :: Int
part2
  = length
  . takeWhile ((<= 50) . distance)
  $ allPoints

input :: Int
input = 1352

main :: IO ()
main = do
  print part1
  print part2
