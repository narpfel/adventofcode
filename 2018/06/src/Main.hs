module Main where

import Data.List (partition)
import Data.List.Split (splitOn)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data Point = Point
  { x :: Int
  , y :: Int
  } deriving (Eq, Ord, Show)

distance :: Point -> Point -> Int
distance p p' = abs (x p - x p') + abs (y p - y p')

count :: Ord a => [a] -> Map a Int
count = Map.unionsWith (+) . map (flip Map.singleton 1)

nearestNeighbours :: [Point] -> Point -> [Point]
nearestNeighbours ps p
  = snd
  . Map.findMin
  . Map.fromListWith (++)
  . map (\p' -> (distance p p', [p']))
  $ ps

uniqueNearestNeighbours :: [Point] -> [Point] -> [Point]
uniqueNearestNeighbours targets
  = concat
  . filter ((== 1) . length)
  . map (nearestNeighbours targets)

allPoints :: [Point] -> ([Point], [Point])
allPoints targets = partition isBorder [Point a b | a <- [0..maxX], b <- [0..maxY]]
  where
    maxX = maximum . map x $ targets
    maxY = maximum . map y $ targets

    isBorder (Point a b) = a == 0 || a == maxX || b == 0 || b == maxY

part1 :: [Point] -> Int
part1 input
  = maximum
  . Map.elems
  . count
  . filter (not . (`Set.member` pointsWithBorder))
  . uniqueNearestNeighbours input
  $ innerPoints
  where
    (border, innerPoints) = allPoints input
    pointsWithBorder = Set.fromList . uniqueNearestNeighbours input $ border

part2 :: [Point] -> Int
part2 input
  = length
  . filter ((<= 10000) . sum . mapM distance input)
  . uncurry (++)
  . allPoints
  $ input

main :: IO ()
main = do
  input <- map ((\[a, b] -> Point a b) . map read . splitOn ", ") . lines <$> readFile "input"
  print . part1 $ input
  print . part2 $ input
