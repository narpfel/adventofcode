module Main (main) where

import Control.Lens hiding (op)
import Control.Monad.State.Strict
import Data.Functor (($>))
import Data.Vector (Vector)
import qualified Data.Vector as Vector

import Au.Parser

type Register = Int
type Offset = Int

type Condition = RegisterFile -> Bool
type RegisterOp = RegisterFile -> RegisterFile

type RegisterAccessor f = (Register -> f Register) -> RegisterFile -> f RegisterFile

data Instruction
  = Op RegisterOp
  | Jmp Condition Offset

type Rom = Vector Instruction

data RegisterFile = RegisterFile
  { _a :: !Register
  , _b :: !Register
  , _c :: !Register
  , _d :: !Register
  , _pc :: !Register
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

cpy :: Parser Char Instruction
cpy = do
  src <- oneArg' "cpy" <* space
  dst <- register
  pure . Op $ (\rf -> rf & dst .~ (rf ^. src))

inc :: Parser Char Instruction
inc = Op . (+~ 1) <$> oneArg "inc"

dec :: Parser Char Instruction
dec = Op . (-~ 1) <$> oneArg "dec"

jnz :: Parser Char Instruction
jnz = conditionalJump "jnz" (/= 0)

conditionalJump :: String -> (Register -> Bool) -> Parser Char Instruction
conditionalJump mnemonic predicate = do
  r <- oneArg' mnemonic <* space
  Jmp (view $ r . to predicate) <$> signedInteger

register :: Functor f => Parser Char (RegisterAccessor f)
register = (word "a" $> a) <> (word "b" $> b) <> (word "c" $> c) <> (word "d" $> d)

immediateOrRegister :: (Contravariant f, Functor f) => Parser Char (RegisterAccessor f)
immediateOrRegister = (to . const <$> signedInteger) <> register

oneArg :: Functor f => String -> Parser Char (RegisterAccessor f)
oneArg mnemonic = word mnemonic *> space *> register

oneArg' :: (Contravariant f, Functor f) => String -> Parser Char (RegisterAccessor f)
oneArg' mnemonic = word mnemonic *> space *> immediateOrRegister

instruction :: Parser Char Instruction
instruction = choice [cpy, inc, dec, jnz]

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
  case (cpu ^. rom) Vector.!? (cpu ^. registerFile . pc) of
    Just instr -> execute instr >> runProgram
    Nothing -> return ()

solve :: Register -> Rom -> Register
solve n = view (registerFile . a) . execState runProgram . Cpu (RegisterFile 0 0 n 0 0)

main :: IO ()
main = do
  Just p <- fmap Vector.fromList . parse program <$> readFile "input"
  print $ solve 0 p
  print $ solve 1 p
