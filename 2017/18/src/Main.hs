module Main (main) where

import Control.Monad.State
import Data.Char (isAlpha, ord)
import Data.Functor ((<&>), ($>))

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
  | Rcv Register
  | Jgz Operand Operand
  deriving (Show)

newtype RegisterFile = RegisterFile (Unboxed.Vector Int) deriving (Show)

unRegisterFile :: RegisterFile -> Unboxed.Vector Int
unRegisterFile (RegisterFile regs) = regs

(//) :: RegisterFile -> (Int, Int) -> RegisterFile
RegisterFile rf // changed = RegisterFile $ rf Unboxed.// [changed]

data Cpu = Cpu
  { registerFile :: !RegisterFile
  , pc :: !Int
  , makeProgress :: [Progress] -> [Progress]
  , rom :: Boxed.Vector Instruction
  }

registerIndexFromName :: Char -> Int
registerIndexFromName = subtract (ord 'a') . ord

immediate :: Parser Operand
immediate = Immediate <$> integer

register :: Parser Register
register = Register . registerIndexFromName <$> matches isAlpha

operand :: Parser Operand
operand = immediate <> (RegisterOperand <$> register)

jgz :: Parser Instruction
jgz = Jgz <$> (word "jgz" *> spaces *> operand) <*> (spaces *> operand)

twoArg :: (Register -> Operand -> Instruction) -> String -> Parser Instruction
twoArg instr mnemonic = instr <$> (word mnemonic *> spaces *> register) <*> (spaces *> operand)

instruction :: Parser Instruction
instruction = choice $
  [ jgz
  , Snd <$> (word "snd" *> spaces *> operand)
  , Rcv <$> (word "rcv" *> spaces *> register)
  ]
  <> map (uncurry twoArg)
    [ (Set, "set")
    , (Add, "add")
    , (Mul, "mul")
    , (Mod, "mod")
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

data Progress = Send Int | Receive Bool deriving (Show, Eq)

isReceive :: Progress -> Bool
isReceive (Receive _) = True
isReceive _ = False

removeFirstReceive :: [Progress] -> [Progress]
removeFirstReceive ps = begin <> drop 1 end
  where
    (begin, end) = break isReceive ps

-- TODO: Try to recurse in `execute` instead of `runProgram` to see if it fixes the
-- `<<loop>>` issue.
execute :: [Progress] -> Instruction -> State Cpu ([Progress], Maybe Progress)
execute input = \case
  Snd op -> do
    input' <- gets makeProgress <&> ($ input)
    send <- Just . Send <$> load op
    pure (input', send)
  Set reg op -> operation (flip const) reg op
  Add reg op -> operation (+) reg op
  Mul reg op -> operation (*) reg op
  Mod reg op -> operation mod reg op
  Rcv reg -> do
    progress <- Just . Receive . (/= 0) <$> load (RegisterOperand reg)
    case input of
      Send sound' : rest -> store reg sound' $> (rest, progress)
      _ -> pure ([], progress)
  Jgz op offset -> do
    value <- load op
    offset' <- load offset
    when (value > 0) $ jump (offset' - 1)
    pure (input, Nothing)
  where
    operation (#) reg op = do
      store reg =<< (#) <$> load (RegisterOperand reg) <*> load op
      pure (input, Nothing)

newCpu :: Int -> ([Progress] -> [Progress]) -> Boxed.Vector Instruction -> Cpu
newCpu p makeProgress' rom' = Cpu
  { registerFile = RegisterFile (Unboxed.replicate 26 0) // (registerIndexFromName 'p', p)
  , pc = 0
  , makeProgress = makeProgress'
  , rom = rom'
  }

runProgram :: [Progress] -> State Cpu [Progress]
runProgram [] = pure []
runProgram input = do
  (input', output) <- (Boxed.!?) <$> gets rom <*> gets pc >>= \case
    Just instr -> execute input instr <* jump 1
    _ -> pure ([], Nothing)
  consMaybe output <$> runProgram input'
    where
      consMaybe Nothing = id
      consMaybe (Just a) = (a:)

part1 :: Boxed.Vector Instruction -> Int
part1 rom = solution
  where
    progress = Receive False : evalState (runProgram progress) (newCpu 0 id rom)
    Send solution
      = last
      . filter (not . isReceive)
      . takeWhile (/= Receive True)
      $ progress

part2 :: Boxed.Vector Instruction -> Int
part2 rom = length . filter (not . isReceive) $ output1
  where
    output0 = evalState (runProgram output1) (newCpu 0 removeFirstReceive rom)
    -- FIXME: Without the `Receive False` the mutual recursion goes into an infinite loop. Why?
    output1 = Receive False : evalState (runProgram output0) (newCpu 1 removeFirstReceive rom)

main :: IO ()
main = do
  Just rom <- parse program <$> readFile "input"
  print . part1 $ rom
  print . part2 $ rom
