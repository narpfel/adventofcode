module Main where

import Data.Char (isUpper)
import Data.Set (Set)
import qualified Data.Set as Set

type Input = Set String

parse :: String -> Input
parse = Set.fromList . map (tail . filter isUpper) . lines

allValues :: Input -> Set Char
allValues = Set.unions . Set.map Set.fromList

childNodes :: Input -> Set Char
childNodes = Set.map last

rootNodes :: Input -> Set Char
rootNodes s = allValues s Set.\\ childNodes s

part1 :: Input -> String
part1 input = case Set.minView . rootNodes $ input of
  Nothing -> ""
  Just (node, _) -> node : rest
    where
      input' = Set.filter ((/= node) . head) input
      rest = if Set.null input'
                then Set.toAscList . childNodes $ input
                else part1 input'

main :: IO ()
main = do
  input <- parse <$> readFile "input"
  putStrLn . part1 $ input
