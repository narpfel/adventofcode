module Main (main) where

import Control.Monad.State.Lazy (execState)
import qualified Data.Vector as Vector

import Au.Parser (parse)

import Cpu (Cpu(..), Rom, program, runProgram)

solve :: Int -> Rom -> Int
solve n = a . execState runProgram . Cpu 0 0 0 n 0

main :: IO ()
main = do
  Just p <- fmap Vector.fromList . parse program <$> readFile "input"
  print $ solve 0 p
  print $ solve 1 p
