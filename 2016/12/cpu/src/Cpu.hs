module Cpu (Cpu(..), Rom, program, runProgram) where

import Control.Monad.State.Lazy (State, modify, get)
import Data.Functor (($>))
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Vector.Mutable (write)

import Au.Parser

data Register = A | B | C | D
data ImmOrReg = Imm Int | Reg Register

data Instruction
  = Cpy ImmOrReg ImmOrReg
  | Inc ImmOrReg
  | Dec ImmOrReg
  | Jnz ImmOrReg ImmOrReg
  | Tgl ImmOrReg

type Rom = Vector Instruction

data Cpu = Cpu
  { pc :: !Int
  , a :: !Int
  , b :: !Int
  , c :: !Int
  , d :: !Int
  , rom :: Rom
  }

signedInteger :: (Read i, Integral i) => Parser Char i
signedInteger = (optional' . char $ '+') >> integer

cpy :: Parser Char Instruction
cpy = Cpy <$> oneArg "cpy" <* space <*> immediateOrRegister

inc :: Parser Char Instruction
inc = Inc <$> oneArg "inc"

dec :: Parser Char Instruction
dec = Dec <$> oneArg "dec"

jnz :: Parser Char Instruction
jnz = Jnz <$> oneArg "jnz" <* space <*> immediateOrRegister

tgl :: Parser Char Instruction
tgl = Tgl <$> oneArg "tgl"

register :: Parser Char ImmOrReg
register = Reg <$> (word "a" $> A) <> (word "b" $> B) <> (word "c" $> C) <> (word "d" $> D)

immediateOrRegister :: Parser Char ImmOrReg
immediateOrRegister = (Imm <$> signedInteger) <> register

oneArg :: String -> Parser Char ImmOrReg
oneArg mnemonic = word mnemonic *> space *> immediateOrRegister

instruction :: Parser Char Instruction
instruction = choice [cpy, inc, dec, jnz, tgl]

program :: Parser Char [Instruction]
program = perLine instruction

execute :: Instruction -> State Cpu ()
execute (Cpy src dst) = modify $ \cpu -> cpu←dst $ cpu→src
execute (Inc reg) = modify $ \cpu -> cpu←reg $ cpu→reg + 1
execute (Dec reg) = modify $ \cpu -> cpu←reg $ cpu→reg - 1
execute (Jnz src offset) = modify $ \cpu -> cpu { pc = newPc cpu }
  where
    newPc cpu
      | cpu→src /= 0 = pc cpu + cpu→offset - 1
      | otherwise = pc cpu
execute (Tgl src) = modify $ \cpu -> cpu { rom = toggle (pc cpu + cpu→src) $ rom cpu }

(→) :: Cpu -> ImmOrReg -> Int
_ → Imm imm = imm
Cpu { .. } → Reg A = a
Cpu { .. } → Reg B = b
Cpu { .. } → Reg C = c
Cpu { .. } → Reg D = d

(←) :: Cpu -> ImmOrReg -> Int -> Cpu
(←) cpu (Imm _) _ = cpu
(←) cpu (Reg A) value = cpu { a = value }
(←) cpu (Reg B) value = cpu { b = value }
(←) cpu (Reg C) value = cpu { c = value }
(←) cpu (Reg D) value = cpu { d = value }

toggle :: Int -> Rom -> Rom
toggle idx rom
  = case maybeInstr of
      Just instr -> Vector.modify (\v -> write v idx $ go instr) rom
      Nothing -> rom
  where
    maybeInstr = rom Vector.!? idx
    go (Cpy a b) = Jnz a b
    go (Inc reg) = Dec reg
    go (Dec reg) = Inc reg
    go (Jnz a b) = Cpy a b
    go (Tgl val) = Inc val

runProgram :: State Cpu ()
runProgram = do
  cpu <- get
  case rom cpu Vector.!? pc cpu of
    Just instr -> execute instr >> updatePc >> runProgram
    Nothing -> pure ()

updatePc :: State Cpu ()
updatePc = modify $ \cpu -> cpu { pc = pc cpu + 1 }
