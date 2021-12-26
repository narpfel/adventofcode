module Main (main) where

import Data.Bits ((.&.))
import Data.Composition ((.:))
import Data.Function (on)

-- INPUT
-- Generator A starts with 116
-- Generator B starts with 299

type Selector = Int -> Bool

lehmerRng :: Int -> Int -> Int -> Int
lehmerRng m a x = (a * x) `mod` m

modulus :: Int
modulus = 2147483647

lsbs :: Int -> Int
lsbs = (.&. 0xffff)

generator :: Int -> Int -> [Int]
generator = drop 1 .: iterate . lehmerRng modulus

solve :: Int -> (Int, Selector) -> (Int, Selector) -> Int
solve len (a, pa) (b, pb) =
  length . filter (== True) . take len $
    zipWith ((==) `on` lsbs)
      (filter pa $ generator 16807 a)
      (filter pb $ generator 48271 b)

part1 :: Int -> Int -> Int
part1 a b = solve 40000000 (a, const True) (b, const True)

isMultipleOf :: Int -> Int -> Bool
isMultipleOf = (== 0) .: flip mod

part2 :: Int -> Int -> Int
part2 a b = solve 5000000 (a, isMultipleOf 4) (b, isMultipleOf 8)

main :: IO ()
main = do
  print $ part1 116 299
  print $ part2 116 299
