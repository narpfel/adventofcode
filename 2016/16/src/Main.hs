module Main (main) where

import Data.List (iterate')
import Data.Composition ((.:))
import Data.Maybe (fromJust)
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as Vector

input :: String
input = "11100010111110100"

discLengthPart1 :: Int
discLengthPart1 = 272

discLengthPart2 :: Int
discLengthPart2 = 35_651_584

parse :: String -> Maybe (Vector Bool)
parse = Vector.mapM fromChar . Vector.fromList
  where
    fromChar '0' = Just False
    fromChar '1' = Just True
    fromChar _ = Nothing

step :: Vector Bool -> Vector Bool
step a = a <> Vector.singleton False <> b
  where
    b = Vector.map not . Vector.reverse $ a

checksum :: Vector Bool -> Vector Bool
checksum xs
  | odd . Vector.length $ xs = xs
  | otherwise
    = checksum
    . Vector.ifilter (even .: const)
    . (Vector.zipWith (==) <*> Vector.tail)
    $ xs

solve :: Int -> Vector Bool -> Vector Bool
solve discLength
  = checksum
  . Vector.take discLength
  . head
  . dropWhile ((< discLength) . Vector.length)
  . iterate' step

toChar :: Bool -> Char
toChar False = '0'
toChar True = '1'

solution :: Int -> String
solution discLength
  = Vector.toList
  . Vector.map toChar
  . solve discLength
  . fromJust
  . parse
  $ input

main :: IO ()
main = do
  putStrLn . solution $ discLengthPart1
  putStrLn . solution $ discLengthPart2
