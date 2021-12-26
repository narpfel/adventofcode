module Main (main) where

import Data.Function (on)
import qualified Data.Map.Strict as Map
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Monoid (Sum(..))

countLetters :: String -> IntSet
countLetters
  = IntSet.fromList
  . Map.elems
  . Map.unionsWith (+)
  . map (flip Map.singleton 1)

both :: (a -> b) -> (a, a) -> (b, b)
both f (a, a') = (f a, f a')

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (a:as) = map (a,) as ++ pairs as

distinctIndices :: String -> String -> IntSet
distinctIndices s1 s2 = IntSet.fromList
  [ index
  | (index, c1, c2) <- zip3 [0..] s1 s2
  , c1 /= c2
  ]

dropIndices :: IntSet -> [a] -> [a]
dropIndices indices xs =
  [ x
  | (index, x) <- zip [0..] xs
  , index `IntSet.notMember` indices
  ]

part1 :: [String] -> Int
part1
  = uncurry ((*) `on` getSum)
  . foldMap (\s -> both (Sum . fromEnum . flip IntSet.member s) (2, 3))
  . map countLetters

part2 :: [String] -> String
part2 input = head
  [ dropIndices indices s
  | (s, s') <- pairs input
  , let indices = distinctIndices s s'
  , IntSet.size indices == 1
  ]

main :: IO ()
main = do
  input <- lines <$> readFile "input"
  print . part1 $ input
  putStrLn . part2 $ input
