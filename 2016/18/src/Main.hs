module Main (main) where

import Data.List (iterate')
import Data.Maybe (mapMaybe)

import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as Vector

parse :: Char -> Maybe Bool
parse '^' = Just False
parse '.' = Just True
parse _ = Nothing

step :: Vector Bool -> Vector Bool
step = (Vector.zipWith3 nextState <*> Vector.init <*> Vector.drop 2) . withWalls
  where
    withWalls = Vector.cons True . flip Vector.snoc True

nextState :: Bool -> Bool -> Bool -> Bool
nextState False False True = False
nextState True False False = False
nextState False True True = False
nextState True True False = False
nextState _ _ _ = True

safeTiles :: Int -> Vector Bool -> Int
safeTiles n
  = sum
  . map (Vector.sum . Vector.map fromEnum)
  . take n
  . iterate' step

solve :: Int -> String -> Int
solve n = safeTiles n . Vector.fromList . mapMaybe parse

main :: IO ()
main = do
  input <- readFile "input"
  print . solve 40 $ input
  print . solve 400_000 $ input
