module Main where

import Control.Applicative (many)
import Control.Monad (join)
import Data.List (findIndices, transpose)
import Data.List.Split (chunksOf)

import Au.Parser

type Triangle = (Integer, Integer, Integer)

triangle :: Tokenizer Triangle
triangle = (,,) <$> spacedInteger <*> spacedInteger <*> spacedInteger
  where
    spacedInteger = many space >> integer

triangles :: Tokenizer [Triangle]
triangles = perLine triangle

checkTriangle :: Triangle -> Bool
checkTriangle (a, b, c) = and [a + b > c, a + c > b, b + c > a]

countPossible :: [Triangle] -> Int
countPossible = length . findIndices id . map checkTriangle

toList :: (a, a, a) -> [a]
toList (x, y, z) = [x, y ,z]

fromList :: [a] -> (a, a, a)
fromList [x, y, z] = (x, y, z)
fromList _ = error "This case is impossible"

main :: IO ()
main = do
    Just triangles <- parse triangles <$> readFile "input"
    print . countPossible $ triangles
    print . countPossible . map fromList . chunksOf 3 . join . transpose . map toList $ triangles
