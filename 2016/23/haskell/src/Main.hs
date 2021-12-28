module Main (main) where

import Control.Monad.State.Lazy (execState)
import qualified Data.Vector as Vector

import Au.Parser (parse)

import Cpu (Cpu(a), Rom, makeCpu, program, runProgram)

solve :: Int -> Rom -> Int
solve n = a . execState runProgram . makeCpu n 0 0 0

main :: IO ()
main = do
  Just p <- fmap Vector.fromList . parse program <$> readFile "input"
  print $ solve 7 p
  -- TODO: This takes ~45 seconds. Implement macro-op fusion for inc/dec/jnz → add
  -- and cpy/add/dec/jnz → mul. `tgl` requires unfusing, applying the toggle and then re-fusing.
  -- Pad with `nop`s to keep jump targets stable, jumping into the loop should also unfuse.
  print $ solve 12 p
