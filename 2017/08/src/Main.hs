module Main (main) where

import Au.Parser
import Control.Monad.State
import qualified Data.Map.Strict as Map
import Text.Show.Functions ()

data Instruction = Instruction
  { registerName :: String
  , update :: Integer -> Integer
  , predicateRegisterName :: String
  , predicate :: Integer -> Bool
  } deriving (Show)

selectUpdateFunction :: String -> (Integer -> Integer -> Integer)
selectUpdateFunction "inc" = (+)
selectUpdateFunction "dec" = flip (-)
selectUpdateFunction _ = undefined

selectPredicate :: String -> (Integer -> Integer -> Bool)
selectPredicate ">" = (>)
selectPredicate ">=" = (>=)
selectPredicate "<" = (<)
selectPredicate "<=" = (<=)
selectPredicate "==" = (==)
selectPredicate "!=" = (/=)
selectPredicate _ = undefined

instruction :: Tokenizer Instruction
instruction = Instruction
  <$> alphabetical
  <*> (space >> updateFunction)
  <*> (word " if " >> alphabetical)
  <*> (space >> predicate')
    where
      updateFunction = (selectUpdateFunction <$> alphabetical) <*> (space >> integer)
      predicate' = (flip . selectPredicate <$> operator) <*> (space >> integer)

instructions :: Tokenizer [Instruction]
instructions = perLine instruction

getValue :: String -> Map.Map String Integer -> Integer
getValue = Map.findWithDefault 0

runInstruction :: Instruction -> State (Map.Map String Integer) Integer
runInstruction instr = do
  registers <- get
  let name = registerName instr
  when (predicate instr $ getValue (predicateRegisterName instr) registers) $
    modify =<< Map.insert name . update instr . getValue name <$> get
  maximum . Map.elems <$> get

main :: IO ()
main = do
  Just instrs <- parse instructions <$> readFile "input"
  let maximums = evalState (mapM runInstruction instrs) Map.empty
  print . last $ maximums
  print . maximum $ maximums
