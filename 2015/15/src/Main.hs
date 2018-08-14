module Main where

import Control.Applicative (some)
import Data.Char (isLetter)
import Data.Composition ((.:))
import Data.Foldable (product)
import Data.List (genericReplicate)
import Data.Matrix
import Data.Maybe (fromJust)
import Data.Vector (toList)

import Au.Parser

ingredients :: Tokenizer [[Integer]]
ingredients = separatedBy' newline line

line :: Tokenizer [Integer]
line =
  alphabetical
  >> word ": "
  >> mapM property ["capacity", "durability", "flavor", "texture", "calories"]

property :: String -> Tokenizer Integer
property s = word s *> space *> integer <* optional (word ", ")

score :: Matrix Integer -> Matrix Integer -> Integer
score = product . fmap (max 0) .: multStd

maxScore :: [(a, Integer)] -> Integer
maxScore = maximum . map snd

possibleCombinations :: Integer -> Matrix Integer -> [([Integer], Integer)]
possibleCombinations n properties =
  [(a, score (fromLists [a]) ingredients) | a <- amounts]
  where
    ingredients =
      submatrix 1 (nrows properties) 1 (ncols properties - 1) properties
    amounts
      = filter ((== n) . sum)
      . sequence
      . genericReplicate (nrows ingredients)
      $ [0 .. n]

part1 :: Matrix Integer -> Integer
part1 = maxScore . possibleCombinations 100

part2 :: Matrix Integer -> Integer
part2 properties =
  maxScore
    [ (calories, score)
    | (amounts, score) <- possibleCombinations 100 properties
    , let calories = sum [a * c | a <- amounts | c <- caloriesPerIngredient]
    , calories == 500
    ]
  where
    caloriesPerIngredient = Data.Vector.toList (getCol (ncols properties) properties)

main :: IO ()
main = do
  ingrs <- fromLists . fromJust . parse ingredients <$> readFile "input"
  print $ part1 ingrs
  print $ part2 ingrs
