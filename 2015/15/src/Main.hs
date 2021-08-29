module Main (main) where

import Control.Monad (replicateM)
import Data.Bifunctor (bimap)
import Data.Composition ((.:))
import Data.Maybe (fromJust)
import qualified Numeric.LinearAlgebra.HMatrix as M
import Numeric.LinearAlgebra.HMatrix (Matrix, Vector, Z)

import Au.Parser

ingredients :: Tokenizer [[Z]]
ingredients = separatedBy' newline line

line :: Tokenizer [Z]
line =
  alphabetical
  >> word ": "
  >> mapM property ["capacity", "durability", "flavor", "texture", "calories"]

property :: String -> Tokenizer Z
property s = word s *> space *> integer <* optional (word ", ")

score :: Vector Z -> Matrix Z -> Z
score = M.prodElements . M.cmap (max 0) .: (M.<#)

possibleCombinations :: Z -> Matrix Z -> [(Vector Z, Z)]
possibleCombinations n ingrs =
  [(amountPerIngredient, score amountPerIngredient ingrs) | amountPerIngredient <- amounts]
  where
    amounts
      = map M.fromList
      . filter ((== n) . sum)
      . replicateM (M.rows ingrs)
      $ [0 .. n]

part1 :: [(Vector Z, Z)] -> Z
part1 = maximum . map snd

part2 :: [(Vector Z, Z)] -> Vector Z -> Z
part2 combinations caloriesPerIngredient =
  maximum
    [ score'
    | (amounts, score') <- combinations
    , let calories = amounts M.<.> caloriesPerIngredient
    , calories == 500
    ]

unsnoc :: [a] -> ([a], a)
unsnoc xs = (init xs, last xs)

main :: IO ()
main = do
  (ingrs, caloriesPerIngredient)
    <- bimap M.fromLists M.fromList
    . unzip
    . map unsnoc
    . fromJust
    . parse ingredients
    <$> readFile "input"
  let combinations = possibleCombinations 100 ingrs
  print $ part1 combinations
  print $ part2 combinations caloriesPerIngredient
