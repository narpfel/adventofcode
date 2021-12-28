module Cpu (Cpu(..), Rom, makeCpu, program, runProgram) where

import Control.Monad (when)
import Control.Monad.State.Lazy (State, modify, get, gets)
import Data.Functor (($>))
import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import Data.Vector.Mutable (write)

import Au.Parser

data Register = A | B | C | D deriving Eq
data ImmOrReg = Imm Int | Reg Register deriving Eq

data Instruction
  = Cpy ImmOrReg ImmOrReg
  | Inc ImmOrReg
  | Dec ImmOrReg
  | Jnz ImmOrReg ImmOrReg
  | Tgl ImmOrReg
  | Add Register Register
  | Nop
  deriving Eq

type Rom = Vector Instruction

data Cpu = Cpu
  { pc :: !Int
  , a :: !Int
  , b :: !Int
  , c :: !Int
  , d :: !Int
  , rom :: Rom
  , originalRom :: Rom
  , poisoned :: Vector Bool
  }

makeCpu :: Int -> Int -> Int -> Int -> Rom -> Cpu
makeCpu a b c d rom = Cpu
  { pc = 0
  , a = a
  , b = b
  , c = c
  , d = d
  , rom = optimisedRom
  , originalRom = rom
  , poisoned = poisoned'
  }
    where
      (optimisedRom, poisoned') = optimise rom

optimise :: Rom -> (Rom, Vector Bool)
optimise rom = (optimisedRom, poisoned')
  where
    optimisedRom = Vector.fromList . go . Vector.toList $ rom
    poisoned' = Vector.zipWith shouldBePoisoned rom optimisedRom

    go [] = []
    go (Inc (Reg dst) : Dec (Reg src) : Jnz (Reg c) (Imm (-2)) : rest) | src == c
      = Add dst src : Nop : Nop : go rest
    go (Dec (Reg src) : Inc (Reg dst) : Jnz (Reg c) (Imm (-2)) : rest) | src == c
      = Add dst src : Nop : Nop : go rest
    go (instr : rest) = instr : go rest

    shouldBePoisoned instr optimisedInstr
      = instr /= optimisedInstr
        && isOptimisedInstr optimisedInstr

    isOptimisedInstr = \case
      (Add _ _) -> True
      Nop -> True
      _ -> False

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
execute (Jnz src offset) = do
  newPc <- gets $ \cpu -> pc cpu + cpu→offset - 1
  shouldJump <- gets $ (/= 0) . (→src)
  when shouldJump $ deoptimiseIfPoisoned newPc >> modify (\cpu -> cpu { pc = newPc })
execute (Tgl src) = modify $ \cpu -> cpu { rom = toggle (pc cpu + cpu→src) $ rom cpu }
execute (Add dst src) = modify $ \cpu -> cpu←Reg dst $ cpu→Reg src + cpu→Reg dst
execute Nop = pure ()

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
    go _ = error "cannot toggle optimised instructions"

deoptimiseIfPoisoned :: Int -> State Cpu ()
deoptimiseIfPoisoned idx = do
  isPoisoned <- gets (fromMaybe False . (Vector.!? idx) . poisoned)
  when isPoisoned $ modify (\cpu -> cpu
    { rom = originalRom cpu
    , poisoned = Vector.replicate (Vector.length (poisoned cpu)) False
    })

runProgram :: State Cpu ()
runProgram = do
  cpu <- get
  case rom cpu Vector.!? pc cpu of
    Just instr -> execute instr >> updatePc >> runProgram
    Nothing -> pure ()

updatePc :: State Cpu ()
updatePc = modify $ \cpu -> cpu { pc = pc cpu + 1 }
