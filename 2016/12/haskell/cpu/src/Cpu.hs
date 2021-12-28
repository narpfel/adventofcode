module Cpu (Cpu(a, b, c, d), Rom, makeCpu, program, runProgram) where

import Control.Monad (when)
import Control.Monad.State.Lazy (State, modify', get, gets, lift)
import Control.Monad.Writer.Lazy (WriterT, tell)
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
  | Mul
    { target :: Register
    , unchangedFactor :: Register
    , mutatedFactor :: Register
    , scratch :: Register
    }
  | Nop
  | Out ImmOrReg
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

instance Eq Cpu where
  lhs == rhs = (==)
    (sequence [pc, a, b, c, d] lhs)
    (sequence [pc, a, b, c, d] rhs)

instance Ord Cpu where
  compare lhs rhs = compare
    (sequence [pc, a, b, c, d] lhs)
    (sequence [pc, a, b, c, d] rhs)

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
    optimisedRom = Vector.fromList . go . go . Vector.toList $ rom
    poisoned' = Vector.zipWith shouldBePoisoned rom optimisedRom

    go [] = []
    go (Inc (Reg dst) : Dec (Reg src) : Jnz (Reg c) (Imm (-2)) : rest) | src == c
      = Add dst src : Nop : Nop : go rest
    go (Dec (Reg src) : Inc (Reg dst) : Jnz (Reg c) (Imm (-2)) : rest) | src == c
      = Add dst src : Nop : Nop : go rest
    go
      ( (Cpy (Reg unchangedFactor) (Reg scratch))
      : (Add target alsoScratch)
      : Nop
      : Nop
      : Dec (Reg mutatedFactor)
      : jump@(Jnz (Reg alsoMutatedFactor) (Imm (-5)))
      : rest )
      | scratch == alsoScratch && mutatedFactor == alsoMutatedFactor
      = Mul target unchangedFactor mutatedFactor scratch : Nop : Nop : Nop : Nop : jump : go rest
    go (instr : rest) = instr : go rest

    shouldBePoisoned instr optimisedInstr
      = instr /= optimisedInstr
        && isOptimisedInstr optimisedInstr

    isOptimisedInstr = \case
      (Add _ _) -> True
      Nop -> True
      Mul {} -> True
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

out :: Parser Char Instruction
out = Out <$> oneArg "out"

register :: Parser Char ImmOrReg
register = Reg <$> (word "a" $> A) <> (word "b" $> B) <> (word "c" $> C) <> (word "d" $> D)

immediateOrRegister :: Parser Char ImmOrReg
immediateOrRegister = (Imm <$> signedInteger) <> register

oneArg :: String -> Parser Char ImmOrReg
oneArg mnemonic = word mnemonic *> space *> immediateOrRegister

instruction :: Parser Char Instruction
instruction = choice [cpy, inc, dec, jnz, tgl, out]

program :: Parser Char [Instruction]
program = perLine instruction

execute :: Instruction -> WriterT [(Cpu, Int)] (State Cpu) ()
execute (Cpy src dst) = modify' $ \cpu -> cpu←dst $ cpu→src
execute (Inc reg) = modify' $ \cpu -> cpu←reg $ cpu→reg + 1
execute (Dec reg) = modify' $ \cpu -> cpu←reg $ cpu→reg - 1
execute (Jnz src offset) = do
  newPc <- gets $ \cpu -> pc cpu + cpu→offset - 1
  shouldJump <- gets $ (/= 0) . (→src)
  lift . when shouldJump $ deoptimiseIfPoisoned newPc >> modify' (\cpu -> cpu { pc = newPc })
execute (Tgl src) = modify' $ \cpu -> cpu { rom = toggle (pc cpu + cpu→src) $ rom cpu }
execute (Add dst src) = modify' $ \cpu -> cpu←Reg dst $ cpu→Reg src + cpu→Reg dst
execute Mul { .. } = do
  modify' $ \cpu -> cpu←Reg target $ cpu→Reg unchangedFactor * cpu→Reg mutatedFactor
  modify' $ \cpu -> cpu←Reg scratch $ 0
  modify' $ \cpu -> cpu←Reg mutatedFactor $ 0
execute Nop = pure ()
execute (Out val) = do
  cpu <- get
  tell [(cpu, cpu→val)]

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
  when isPoisoned $ modify' (\cpu -> cpu
    { rom = originalRom cpu
    , poisoned = Vector.replicate (Vector.length (poisoned cpu)) False
    })

runProgram :: WriterT [(Cpu, Int)] (State Cpu) ()
runProgram = do
  cpu <- get
  case rom cpu Vector.!? pc cpu of
    Just instr -> execute instr >> lift updatePc >> runProgram
    Nothing -> pure ()

updatePc :: State Cpu ()
updatePc = modify' $ \cpu -> cpu { pc = pc cpu + 1 }
