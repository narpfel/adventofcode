module Main (main) where

import Data.Functor (($>))
import Data.List (elemIndex)
import Data.Maybe (fromJust)
import Data.Semigroup (Endo(Endo, appEndo))
import Prelude hiding (Either(..))

import Test.QuickCheck

import Au.Parser hiding (Parser)
import qualified Au.Parser as Au

type Parser = Au.Parser Char

data Direction = Left | Right deriving (Show)

data Scramble
  = SwapPosition Int Int
  | SwapLetter Char Char
  | Rotate Direction Int
  | RotatePosition Char
  | ReversePositions Int Int
  | Move Int Int
  | InvertRotatePosition Char
  deriving (Show)

direction :: Parser Direction
direction = (word "left" $> Left) <> (word "right" $> Right)

swapPosition :: Parser Scramble
swapPosition
  = SwapPosition
  <$> (word "swap position " *> integer)
  <*> (word " with position " *> integer)

swapLetter :: Parser Scramble
swapLetter
  = SwapLetter
  <$> (word "swap letter " *> anything)
  <*> (word " with letter " *> anything)

rotate :: Parser Scramble
rotate
  = Rotate
  <$> (word "rotate " *> direction)
  <*> (word " " *> integer <* word " step" <* optional (word "s"))

rotatePosition :: Parser Scramble
rotatePosition
  = RotatePosition
  <$> (word "rotate based on position of letter " *> anything)

reversePositions :: Parser Scramble
reversePositions
  = ReversePositions
  <$> (word "reverse positions " *> integer)
  <*> (word " through " *> integer)

move :: Parser Scramble
move
  = Move
  <$> (word "move position " *> integer)
  <*> (word " to position " *> integer)

parseScramble :: Parser Scramble
parseScramble = choice [swapPosition, swapLetter, rotate, rotatePosition, reversePositions, move]

scramble :: Scramble -> String -> String
scramble (SwapPosition i j) cs
  = [ case n of
        _ | n == i -> cs !! j
        _ | n == j -> cs !! i
        _ -> c
    | (n, c) <- zip [0..] cs
    ]
scramble (SwapLetter a b) cs
  = flip scramble cs
  . fromJust
  $ SwapPosition
    <$> a `elemIndex` cs
    <*> b `elemIndex` cs
scramble (Rotate Left i) cs = end <> begin
  where
    (begin, end) = splitAt (i `mod` length cs) cs
scramble (Rotate Right i) cs = scramble (Rotate Left (length cs - i)) cs
scramble (RotatePosition c) cs = scramble (Rotate Right (1 + i + if i >= 4 then 1 else 0)) cs
  where
    i = fromJust $ c `elemIndex` cs
scramble (ReversePositions i j) cs = begin <> reverse middle <> end
  where
    (begin, rest) = splitAt i cs
    (middle, end) = splitAt (j - i + 1) rest
scramble (Move i j) cs = begin <> [c] <> end
  where
    c = cs !! i
    (begin, end) = splitAt j [c' | (n, c') <- zip [0..] cs, n /= i]
scramble (InvertRotatePosition c) cs = scramble (Rotate Right j) cs
  where
    Just i = c `elemIndex` cs
    -- FIXME: These values were determined manually and are only valid
    -- for length 8 passwords
    j = [7, -1, 2, -2, 1, -3, 0, -4] !! i

invert :: Scramble -> Scramble
invert (SwapPosition i j) = SwapPosition i j
invert (SwapLetter a b) = SwapLetter a b
invert (Rotate Left i) = Rotate Right i
invert (Rotate Right i) = Rotate Left i
invert (RotatePosition c) = InvertRotatePosition c
invert (ReversePositions i j) = ReversePositions i j
invert (Move i j) = Move j i
invert (InvertRotatePosition _) = error "InvertRotatePosition is not meant to be inverted"

unScramble :: Scramble -> String -> String
unScramble = scramble . invert

runScramble :: [Scramble] -> String -> String
runScramble = appEndo . foldMap (Endo . scramble)

runUnScramble :: [Scramble] -> String -> String
runUnScramble = appEndo . foldMap (Endo . unScramble) . reverse

password :: String
password = "abcdefgh"

scrambledPassword :: String
scrambledPassword = "fbgdceah"

readInput :: String -> IO [Scramble]
readInput filename
  = reverse
  . fromJust
  . parse (perLine parseScramble)
  <$> readFile filename

main :: IO ()
main = do
  runTests >>= \case
    Success {} -> pure ()
    failure -> error $ "QuickCheck failed with " <> show failure

  inputTest <- readInput "input_test"
  case runScramble inputTest "abcde" of
    "decab" -> pure ()
    _ -> error "test input produced invalid result"

  input <- readInput "input"
  let part1 = runScramble input password
  putStrLn part1

  case runUnScramble input part1 of
    "abcdefgh" -> pure ()
    _ -> error "unscrambling part1 solution failed"

  putStrLn . runUnScramble input $ scrambledPassword


newtype Input = Input String deriving (Show)

instance Arbitrary Direction where
  arbitrary = elements [Left, Right]

instance Arbitrary Scramble where
  arbitrary = oneof
    [ SwapPosition <$> ixs <*> ixs
    , SwapLetter <$> chars <*> chars
    , Rotate <$> arbitrary <*> ixs
    , RotatePosition <$> chars
    , do
        i <- ixs
        j <- ixs `suchThat` (>= i)
        pure $ ReversePositions i j
    , Move <$> ixs <*> ixs
    ]
      where
        ixs = elements [0..7]
        chars = elements ['a'..'h']

instance Arbitrary Input where
  arbitrary = Input <$> shuffle ['a'..'h']

prop_unScramble :: Scramble -> Input -> Bool
prop_unScramble s (Input cs) = (unScramble s . scramble s) cs == cs

runTests :: IO Result
runTests = quickCheckWithResult stdArgs { maxSuccess = 1000, chatty = False } prop_unScramble
