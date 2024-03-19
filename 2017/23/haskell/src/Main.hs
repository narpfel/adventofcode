module Main (main) where

import Control.Monad (when)
import Control.Monad.State
import Data.Char (isAlpha, ord)

import qualified Data.Vector as Boxed
import qualified Data.Vector.Unboxed as Unboxed

import qualified Au.Parser as Au
import Au.Parser hiding (Parser)

type Parser = Au.Parser Char

newtype Register = Register Int deriving (Show)

data Operand = RegisterOperand Register | Immediate Int deriving (Show)

data Instruction
  = Set Register Operand
  | Sub Register Operand
  | Mul Register Operand
  | Jnz Operand Operand
  deriving (Show)

newtype RegisterFile = RegisterFile (Unboxed.Vector Int) deriving (Show)

unRegisterFile :: RegisterFile -> Unboxed.Vector Int
unRegisterFile (RegisterFile regs) = regs

(//) :: RegisterFile -> (Int, Int) -> RegisterFile
RegisterFile rf // changed = RegisterFile $ rf Unboxed.// [changed]

data Cpu = Cpu
  { registerFile :: !RegisterFile
  , pc :: !Int
  , rom :: Boxed.Vector Instruction
  , mulsExecuted :: !Int
  }

registerIndexFromName :: Char -> Int
registerIndexFromName = subtract (ord 'a') . ord

immediate :: Parser Operand
immediate = Immediate <$> integer

register :: Parser Register
register = Register . registerIndexFromName <$> matches isAlpha

operand :: Parser Operand
operand = immediate <> (RegisterOperand <$> register)

jnz :: Parser Instruction
jnz = Jnz <$> (word "jnz" *> spaces *> operand) <*> (spaces *> operand)

twoArg :: (Register -> Operand -> Instruction) -> String -> Parser Instruction
twoArg instr mnemonic = instr <$> (word mnemonic *> spaces *> register) <*> (spaces *> operand)

instruction :: Parser Instruction
instruction = choice $
  jnz : map (uncurry twoArg)
    [ (Set, "set")
    , (Sub, "sub")
    , (Mul, "mul")
    ]

program :: Parser (Boxed.Vector Instruction)
program = Boxed.fromList <$> perLine instruction

load :: Operand -> State Cpu Int
load (RegisterOperand (Register r)) = gets $ (Unboxed.! r) . unRegisterFile . registerFile
load (Immediate i) = pure i

store :: Register -> Int -> State Cpu ()
store (Register r) value
  = modify (\cpu@Cpu { .. } -> cpu { registerFile = registerFile // (r, value) })

jump :: Int -> State Cpu ()
jump n = modify (\cpu@Cpu { .. } -> cpu { pc = pc + n })

mulExecuted :: State Cpu ()
mulExecuted = modify (\cpu@Cpu { .. } -> cpu { mulsExecuted = mulsExecuted + 1 })

execute :: Instruction -> State Cpu ()
execute = \case
  Set reg op -> operation (flip const) reg op
  Sub reg op -> operation (-) reg op
  Mul reg op -> mulExecuted *> operation (*) reg op
  Jnz op offset -> do
    value <- load op
    offset' <- load offset
    when (value /= 0) $ jump (offset' - 1)
    pure ()
  where
    operation (#) reg op = do
      store reg =<< (#) <$> load (RegisterOperand reg) <*> load op
      pure ()

newCpu :: Int -> Boxed.Vector Instruction -> Cpu
newCpu a rom' = Cpu
  { registerFile = RegisterFile (Unboxed.replicate 8 0) // (registerIndexFromName 'a', a)
  , pc = 0
  , mulsExecuted = 0
  , rom = rom'
  }

runProgram :: State Cpu ()
runProgram = do
  (Boxed.!?) <$> gets rom <*> gets pc >>= \case
    Just instr -> execute instr *> jump 1 *> runProgram
    _ -> pure ()

part1 :: Boxed.Vector Instruction -> Int
part1 = mulsExecuted . execState runProgram . newCpu 0

isNotPrime :: Int -> Bool
isNotPrime n = any ((== 0) . (n `mod`)) $ 2 : [3, 5 .. n `div` 2]

part2 :: Boxed.Vector Instruction -> Int
part2 instrs = length . filter isNotPrime $ [b, b - step .. c]
  where
    Set _ (Immediate initialB) = instrs Boxed.! 0
    Mul _ (Immediate m) = instrs Boxed.! 4
    Sub _ (Immediate offset) = instrs Boxed.! 5
    b = initialB * m - offset
    Sub _ (Immediate step) = Boxed.last . Boxed.init $ instrs
    Sub _ (Immediate cOffset) = instrs Boxed.! 7
    c = b - cOffset

main :: IO ()
main = do
  Just rom <- parse program <$> readFile "input"
  print . part1 $ rom
  print . part2 $ rom
