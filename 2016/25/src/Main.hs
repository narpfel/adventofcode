module Main (main) where

import Control.Monad.State.Lazy (evalState)
import Control.Monad.Writer.Lazy (execWriterT)
import qualified Data.Set as Set
import qualified Data.Vector as Vector

import Au.Parser (parse)
import Cpu (Rom, Cpu, runProgram, makeCpu, program)

solve :: Int -> Rom -> Int
solve n rom = if isSolution result then n else solve (n + 1) rom
  where
    result = (evalState . execWriterT) runProgram . makeCpu n 0 0 0 $ rom
    isSolution :: [(Cpu, Int)] -> Bool
    isSolution = go Set.empty . zip (cycle [0, 1])
      where
        go _ [] = False
        go history ((expected, (cpu, output)) : rest)
          | output == expected && cpu `Set.member` history = True
          | output == expected = go (cpu `Set.insert` history) rest
          | otherwise = False

main :: IO ()
main = do
  Just p <- fmap Vector.fromList . parse program <$> readFile "input"
  print $ solve 0 p
