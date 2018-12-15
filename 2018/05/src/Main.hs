module Main where

import Data.Char (toLower, isSpace)
import Data.List (dropWhileEnd, foldl')
import qualified Data.Set as Set
import Criterion.Main

annihilate :: String -> String
annihilate = foldl' f ""
  where
    f "" y = y:""
    f (x:xs) y
      | x /= y && toLower x == toLower y = xs
      | otherwise = y:x:xs

part1 :: String -> Int
part1 = length . annihilate

part2 :: String -> Int
part2 input
  = minimum
  . mapM (\c -> part1 . filter ((/= c) . toLower)) letters
  $ input
    where
      letters = Set.toList . Set.fromList . map toLower $ input

benchmark :: String -> IO ()
benchmark input =
  defaultMain
    [ bgroup "day05"
      [ bench "part1" $ nf part1 input
      , bench "part2" $ nf part2 input
      ]
    ]

main :: IO ()
main = do
  input <- dropWhileEnd isSpace <$> readFile "input"
  print . part1 $ input
  print . part2 $ input
  benchmark input
