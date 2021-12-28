module Main (main) where

import Control.Monad.State.Lazy (execState)
import Control.Monad.Writer.Lazy (execWriterT)
import qualified Data.Vector as Vector

import Au.Parser (parse)

import Cpu (Cpu(a), Rom, makeCpu, program, runProgram)

solve :: Int -> Rom -> Int
solve n = a . (execState . execWriterT) runProgram . makeCpu n 0 0 0

main :: IO ()
main = do
  Just p <- fmap Vector.fromList . parse program <$> readFile "input"
  print $ solve 7 p
  print $ solve 12 p
