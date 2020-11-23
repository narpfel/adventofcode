module Main (main) where

import Data.List (foldl')
import Data.List (iterate')
import Data.List.Split (chunksOf)
import Data.Maybe (fromJust)

input :: String
input = "11100010111110100"

discLengthPart1 :: Int
discLengthPart1 = 272

discLengthPart2 :: Int
discLengthPart2 = 35_651_584

parse :: String -> Maybe [Bool]
parse = traverse fromChar
  where
    fromChar '0' = Just False
    fromChar '1' = Just True
    fromChar _ = Nothing

step :: [Bool] -> [Bool]
step a = a <> [False] <> b
  where
    b = map not . reverse $ a

checksum :: [Bool] -> [Bool]
checksum xs
  | odd . length $ xs = xs
  | otherwise = checksum . map (foldl1' (==)) . chunksOf 2 $ xs

foldl1' :: (a -> a -> a) -> [a] -> a
foldl1' _ [] = error "foldl1' of empty list"
foldl1' f (x:xs) = foldl' f x xs

solve :: Int -> [Bool] -> [Bool]
solve discLength
  = checksum
  . take discLength
  . head
  . dropWhile ((< discLength) . length)
  . iterate' step

toChar :: Bool -> Char
toChar False = '0'
toChar True = '1'

solution :: Int -> String
solution discLength = map toChar . solve discLength . fromJust . parse $ input

main :: IO ()
main = do
  putStrLn . solution $ discLengthPart1
  putStrLn "part2: not optimised enough"
