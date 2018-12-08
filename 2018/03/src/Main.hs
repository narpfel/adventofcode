module Main where

import qualified Data.Set as Set

import Au.Parser

data Point = Point
  { x :: Int
  , y :: Int
  }
  deriving (Show, Ord, Eq)

instance Semigroup Point where
  p1 <> p2 = Point (x p1 + x p2) (y p1 + y p2)

invert :: Point -> Point
invert p = Point (negate . x $ p) (negate . y $ p)

(<->) :: Point -> Point -> Point
p1 <-> p2 = p1 <> invert p2

data Rectangle = Rectangle
  { idNumber :: Int
  , topLeft :: Point
  , bottomRight :: Point
  }
  deriving Show

rectangle :: Parser Char Rectangle
rectangle = do
  id' <- word "#" >> integer
  corner <- word " @ " >> point ","
  size <- word ": " >> point "x"
  pure $ Rectangle id' corner (corner <> size)

point :: String -> Parser Char Point
point sep = Point <$> integer <*> (word sep >> integer)

isFlipped :: Rectangle -> Bool
isFlipped r = bottomRight r `isTopLeftOf` topLeft r

isTopLeftOf :: Point -> Point -> Bool
p1 `isTopLeftOf` p2 = x p1 < x p2 && y p1 < y p2

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (a:as) = map (a,) as ++ pairs as

area :: Rectangle -> Int
area r = x diagonal * y diagonal
  where
    diagonal = bottomRight r <-> topLeft r

overlap :: Rectangle -> Rectangle -> Rectangle
overlap (Rectangle _ p1 p2) (Rectangle _ p1' p2') = Rectangle 0 p q
  where
    p = Point (max (x p1) (x p1')) (max (y p1) (y p1'))
    q = Point (min (x p2) (x p2')) (min (y p2) (y p2'))

allPoints :: Rectangle -> [Point]
allPoints r =
  [ Point a b
  | a <- [x . topLeft $ r .. pred . x . bottomRight $ r]
  , b <- [y . topLeft $ r .. pred . y . bottomRight $ r]
  ]

part1 :: [Rectangle] -> Int
part1
  = Set.size
  . Set.fromList
  . concatMap (allPoints . uncurry overlap)
  . pairs

part2 :: [Rectangle] -> Int
part2 rs
  = head
  . Set.elems
  . Set.difference (Set.fromList . map idNumber $ rs)
  . Set.fromList
  . concat
  $ [ [idNumber r1, idNumber r2]
    | (r1, r2) <- pairs rs
    , not . null . allPoints . overlap r1 $ r2
    ]

main :: IO ()
main = do
  Just input <- parse (perLine rectangle) <$> readFile "input"
  print . part1 $ input
  print . part2 $ input
