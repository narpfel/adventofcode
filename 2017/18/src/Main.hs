module Main (main) where

import Control.Monad.State
import Data.Char (isAlpha, ord)
import Data.Coerce (coerce)
import Data.Maybe

import qualified Data.Vector as Boxed
import qualified Data.Vector.Unboxed as Unboxed

import qualified Au.Parser as Au
import Au.Parser hiding (Parser)

type Parser = Au.Parser Char

newtype Register = Register Int deriving (Show)

data Operand = RegisterOperand Register | Immediate Int deriving (Show)

data Instruction
  = Snd Operand
  | Set Register Operand
  | Add Register Operand
  | Mul Register Operand
  | Mod Register Operand
  | Rcv Operand
  | Jgz Operand Operand
  deriving (Show)

newtype RegisterFile = RegisterFile (Unboxed.Vector Int) deriving (Show)

unRegisterFile :: RegisterFile -> Unboxed.Vector Int
unRegisterFile = coerce

data Cpu = Cpu
  { registerFile :: !RegisterFile
  , sound :: !Int
  , pc :: !Int
  }
  deriving (Show)

immediate :: Parser Operand
immediate = Immediate <$> integer

register :: Parser Register
register = Register . (subtract (ord 'a')) . ord <$> matches isAlpha

operand :: Parser Operand
operand = immediate <> (RegisterOperand <$> register)

jgz :: Parser Instruction
jgz = Jgz <$> (word "jgz" *> spaces *> operand) <*> (spaces *> operand)

oneArg :: (Operand -> Instruction) -> String -> Parser Instruction
oneArg instr mnemonic = instr <$> (word mnemonic *> spaces *> operand)

twoArg :: (Register -> Operand -> Instruction) -> String -> Parser Instruction
twoArg instr mnemonic = instr <$> (word mnemonic *> spaces *> register) <*> (spaces *> operand)

instruction :: Parser Instruction
instruction = choice . concat $
  [ [jgz]
  , map (uncurry oneArg) [(Snd, "snd"), (Rcv, "rcv")]
  , map (uncurry twoArg)
    [ (Set, "set")
    , (Add, "add")
    , (Mul, "mul")
    , (Mod, "mod")
    ]
  ]

program :: Parser (Boxed.Vector Instruction)
program = Boxed.fromList <$> perLine instruction

load :: Operand -> State Cpu Int
load (RegisterOperand (Register r)) = gets $ (Unboxed.! r) . unRegisterFile . registerFile
load (Immediate i) = pure i

store :: Register -> Int -> State Cpu ()
store (Register r) value
  = modify' (\cpu @ Cpu { .. } -> cpu { registerFile = update registerFile })
    where
      update rf = RegisterFile (unRegisterFile rf Unboxed.// [(r, value)])

jump :: Int -> State Cpu ()
jump n = modify' (\cpu @ Cpu { .. } -> cpu { pc = pc + n })

execute :: Instruction -> State Cpu (Maybe Int)
execute = \case
  Snd op -> do
    value <- load op
    modify' (\cpu -> cpu { sound = value })
    pure Nothing
  Set reg op -> operation (flip const) reg op
  Add reg op -> operation (+) reg op
  Mul reg op -> operation (*) reg op
  Mod reg op -> operation mod reg op
  Rcv reg -> do
    value <- load reg
    sound' <- gets sound
    pure $ if value /= 0 then Just sound' else Nothing
  Jgz op offset -> do
    value <- load op
    offset' <- load offset
    when (value > 0) $ jump (offset' - 1)
    pure Nothing
  where
    operation (#) reg op = do
      store reg =<< (#) <$> load (RegisterOperand reg) <*> load op
      pure Nothing

runProgram :: Boxed.Vector Instruction -> State Cpu [Maybe Int]
runProgram rom = sequence . repeat $ do
  pc' <- gets pc
  execute (rom Boxed.! pc') <* jump 1

main :: IO ()
main = do
  Just rom <- parse program <$> readFile "input"
  let results
        = evalState (runProgram rom)
        $ Cpu { registerFile = RegisterFile (Unboxed.replicate 26 0), sound = 0, pc = 0 }
  print . head . catMaybes $ results
