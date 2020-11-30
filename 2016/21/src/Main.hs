module Main (main) where

import Data.Functor (($>))
import Data.Maybe (fromJust)
import Data.Semigroup (Endo(Endo, appEndo))
import Prelude hiding (Either(..))

import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as Vector

import Au.Parser hiding (Parser)
import qualified Au.Parser as Au

type Parser = Au.Parser Char

type Scramble = Vector Char -> Vector Char

data Direction = Left | Right

direction :: Parser Direction
direction = (word "left" $> Left) <> (word "right" $> Right)

swapPosition :: Parser Scramble
swapPosition
  = swapPosition'
  <$> (word "swap position " *> integer)
  <*> (word " with position " *> integer)

swapLetter :: Parser Scramble
swapLetter
  = swapLetter'
  <$> (word "swap letter " *> anything)
  <*> (word " with letter " *> anything)

rotate :: Parser Scramble
rotate
  = rotate'
  <$> (word "rotate " *> direction)
  <*> (word " " *> integer <* word " step" <* optional (word "s"))

rotatePosition :: Parser Scramble
rotatePosition
  = rotatePosition'
  <$> (word "rotate based on position of letter " *> anything)

reversePositions :: Parser Scramble
reversePositions
  = reversePositions'
  <$> (word "reverse positions " *> integer)
  <*> (word " through " *> integer)

move :: Parser Scramble
move
  = move'
  <$> (word "move position " *> integer)
  <*> (word " to position " *> integer)

scramble :: Parser Scramble
scramble = choice [swapPosition, swapLetter, rotate, rotatePosition, reversePositions, move]

swapPosition' :: Int -> Int -> Scramble
swapPosition' i j cs = cs Vector.// [(i, cs Vector.! j), (j, cs Vector.! i)]

swapLetter' :: Char -> Char -> Scramble
swapLetter' a b cs
  = fromJust
  $ swapPosition'
    <$> a `Vector.elemIndex` cs
    <*> b `Vector.elemIndex` cs
    <*> pure cs

rotate' :: Direction -> Int -> Scramble
rotate' Left i cs = Vector.drop i' cs <> Vector.take i' cs
  where
    i' = i `mod` Vector.length cs
rotate' Right i cs = rotate' Left (Vector.length cs - i) cs

rotatePosition' :: Char -> Scramble
rotatePosition' c cs = rotate' Right (1 + i + if i >= 4 then 1 else 0) cs
  where
    i = fromJust $ c `Vector.elemIndex` cs

reversePositions' :: Int -> Int -> Scramble
reversePositions' i j cs
  = Vector.take i cs
  <> (Vector.reverse . Vector.take (j - i + 1) . Vector.drop i) cs
  <> Vector.drop (j + 1) cs

move' :: Int -> Int -> Scramble
move' i j cs = begin <> Vector.singleton c <> end
  where
    c = cs Vector.! i
    (begin, end) = Vector.splitAt j . Vector.ifilter (\n _ -> n /= i) $ cs

password :: String
password = "abcdefgh"

readInput :: String -> IO Scramble
readInput filename
  = appEndo
  . foldMap Endo
  . reverse
  . fromJust
  . parse (perLine scramble)
  <$> readFile filename

main :: IO ()
main = do
  inputTest <- readInput "input_test"
  case Vector.toList (inputTest $ Vector.fromList "abcde") of
    "decab" -> pure ()
    _ -> error "test input produced invalid result"
  input <- readInput "input"
  putStrLn . Vector.toList . input . Vector.fromList $ password
