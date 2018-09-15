module Main (main) where

import Control.Lens hiding (op)
import Control.Monad.State
import Data.Functor (($>))

import Au.Parser

type Register = Integer
type Offset = Integer

type Condition = RegisterFile -> Bool
type RegisterOp = RegisterFile -> RegisterFile

data Instruction
  = Op RegisterOp
  | Jmp Condition Offset

type Rom = [Instruction]

data RegisterFile = RegisterFile
  { _a :: Register
  , _b :: Register
  , _pc :: Register
  }

data Cpu = Cpu
  { _registerFile :: RegisterFile
  , _rom :: Rom
  }

makeLenses ''Instruction
makeLenses ''RegisterFile
makeLenses ''Cpu

signedInteger :: (Read i, Integral i) => Parser Char i
signedInteger = (optional' . char $ '+') >> integer

hlf :: Parser Char Instruction
hlf = Op . (%~ (`div` 2)) <$> oneArg "hlf"

tpl :: Parser Char Instruction
tpl = Op . (*~ 3) <$> oneArg "tpl"

inc :: Parser Char Instruction
inc = Op . (+~ 1) <$> oneArg "inc"

jmp :: Parser Char Instruction
jmp = Jmp (const True) <$> (word "jmp " >> signedInteger)

jie :: Parser Char Instruction
jie = conditionalJump "jie" even

jio :: Parser Char Instruction
jio = conditionalJump "jio" (== 1)

conditionalJump :: String -> (Register -> Bool) -> Parser Char Instruction
conditionalJump mnemonic predicate = do
  r <- oneArg mnemonic <* word ", "
  Jmp (view $ r . to predicate) <$> signedInteger

register :: Functor f => Parser Char ((Register -> f Register) -> RegisterFile -> f RegisterFile)
register = (word "a" $> a) <> (word "b" $> b)

oneArg :: Functor f => String -> Parser Char ((Register -> f Register) -> RegisterFile -> f RegisterFile)
oneArg mnemonic = word mnemonic >> space >> register

instruction :: Parser Char Instruction
instruction = choice [hlf, tpl, inc, jmp, jie, jio]

program :: Parser Char [Instruction]
program = perLine instruction

execute :: Instruction -> State Cpu ()
execute (Op operation) = modify $ (registerFile %~ operation) . (registerFile . pc +~ 1)
execute (Jmp condition offset) = do
  takeJump <- gets . view $ registerFile . to condition
  modify (registerFile . pc +~ if takeJump then offset else 1)

runProgram :: State Cpu ()
runProgram = do
  cpu <- get
  case cpu ^? rom . element (cpu ^. registerFile . pc . to fromInteger) of
    Just instr -> execute instr >> runProgram
    Nothing -> return ()

solve :: Integer -> [Instruction] -> Integer
solve n = view (registerFile . b) . execState runProgram . Cpu (RegisterFile n 0 0)

main :: IO ()
main = do
  Just p <- parse program <$> readFile "input"
  print $ solve 0 p
  print $ solve 1 p
