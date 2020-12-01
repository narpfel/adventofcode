module Main (main) where

import Data.Functor (($>))
import Data.Maybe (fromJust)
import Data.Semigroup (Endo(Endo, appEndo))
import Prelude hiding (Either(..))

import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as Vector

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

scramble :: Scramble -> Vector Char -> Vector Char
scramble (SwapPosition i j) cs = cs Vector.// [(i, cs Vector.! j), (j, cs Vector.! i)]
scramble (SwapLetter a b) cs
  = flip scramble cs
  . fromJust
  $ SwapPosition
    <$> a `Vector.elemIndex` cs
    <*> b `Vector.elemIndex` cs
scramble (Rotate Left i) cs = Vector.drop i' cs <> Vector.take i' cs
  where
    i' = i `mod` Vector.length cs
scramble (Rotate Right i) cs = scramble (Rotate Left (Vector.length cs - i)) cs
scramble (RotatePosition c) cs = scramble (Rotate Right (1 + i + if i >= 4 then 1 else 0)) cs
  where
    i = fromJust $ c `Vector.elemIndex` cs
scramble (ReversePositions i j) cs
  = Vector.take i cs
  <> (Vector.reverse . Vector.take (j - i + 1) . Vector.drop i) cs
  <> Vector.drop (j + 1) cs
scramble (Move i j) cs = begin <> Vector.singleton c <> end
  where
    c = cs Vector.! i
    (begin, end) = Vector.splitAt j . Vector.ifilter (\n _ -> n /= i) $ cs
scramble (InvertRotatePosition c) cs = scramble (Rotate Right j) cs
  where
    Just i = c `Vector.elemIndex` cs
    -- FIXME: These values were determined manually and are only valid
    -- for length 8 passwords
    j = [7, -1, 2, -2, 1, -3, 0, -4] !! i

unScramble :: Scramble -> Scramble
unScramble (SwapPosition i j) = SwapPosition i j
unScramble (SwapLetter a b) = SwapLetter a b
unScramble (Rotate Left i) = Rotate Right i
unScramble (Rotate Right i) = Rotate Left i
unScramble (RotatePosition c) = InvertRotatePosition c
unScramble (ReversePositions i j) = ReversePositions i j
unScramble (Move i j) = Move j i
unScramble (InvertRotatePosition _) = error "InvertRotatePosition is not meant to be inverted"

password :: String
password = "abcdefgh"

scrambledPassword :: String
scrambledPassword = "fbgdceah"

readInput :: String -> IO (Vector Char -> Vector Char)
readInput filename
  = appEndo
  . foldMap (Endo . scramble)
  . reverse
  . fromJust
  . parse (perLine parseScramble)
  <$> readFile filename

readReverse :: String -> IO (Vector Char -> Vector Char)
readReverse filename
  = appEndo
  . foldMap (Endo . scramble . unScramble)
  . fromJust
  . parse (perLine parseScramble)
  <$> readFile filename

main :: IO ()
main = do
  runTests >>= \case
    Success { .. } -> pure ()
    failure -> error $ "QuickCheck failed with " <> show failure

  inputTest <- readInput "input_test"
  case Vector.toList (inputTest $ Vector.fromList "abcde") of
    "decab" -> pure ()
    _ -> error "test input produced invalid result"

  input <- readInput "input"
  let part1 = Vector.toList . input . Vector.fromList $ password
  putStrLn part1

  reverseInput <- readReverse "input"
  case Vector.toList . reverseInput . Vector.fromList $ part1 of
    "abcdefgh" -> pure ()
    _ -> error "unscrambling part1 solution failed"

  putStrLn . Vector.toList . reverseInput . Vector.fromList $ scrambledPassword


newtype Input = Input (Vector Char) deriving (Show)

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
  arbitrary = Input . Vector.fromList <$> shuffle ['a'..'h']

prop_unScramble :: Scramble -> Input -> Bool
prop_unScramble s (Input cs) = (scramble (unScramble s) . scramble s) cs == cs

runTests :: IO Result
runTests = quickCheckWithResult stdArgs { maxSuccess = 1000, chatty = False } prop_unScramble
