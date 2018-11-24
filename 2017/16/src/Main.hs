module Main where

import Control.Monad.State.Strict
import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap

import Au.Parser

data Move
  = Spin Index
  | Exchange Index Index
  | Partner Name Name
  deriving Show

type Index = Int
type Name = Char
type Programs = Bimap Index Name

moves :: Parser Char [Move]
moves = separatedBy' (word ",") move <* anything

move :: Parser Char Move
move = spin <> exchange <> partner

spin :: Parser Char Move
spin = Spin <$> (word "s" >> integer)

exchange :: Parser Char Move
exchange = Exchange <$> (word "x" >> integer) <*> (word "/" >> integer)

partner :: Parser Char Move
partner = Partner <$> (word "p" >> anything) <*> (word "/" >> anything)

startArrangement :: Programs
startArrangement = Bimap.fromList [(i, l) | i <- [0..15] | l <- ['a'..]]

executeMove :: Move -> State Programs ()
executeMove (Spin n) = do
  newElems <- rotate n . map snd <$> gets Bimap.assocs
  keys <- gets Bimap.keys
  put . Bimap.fromList $ zip keys newElems
executeMove (Exchange n k) = do
  p <- gets (Bimap.! n)
  q <- gets (Bimap.! k)
  modify' $ Bimap.insert k p
  modify' $ Bimap.insert n q
executeMove (Partner p q) = do
  n <- gets (Bimap.!> p)
  k <- gets (Bimap.!> q)
  modify' $ Bimap.insert k p
  modify' $ Bimap.insert n q

rotate :: Int -> [a] -> [a]
rotate n as = drop (l - n) as ++ take (l - n) as
  where
    l = length as

arrangements :: [Move] -> [String]
arrangements input = map (map snd . Bimap.assocs) $ iterate f startArrangement
  where
    f :: Programs -> Programs
    f = execState . mapM_ executeMove $ input

findCycleLength :: Eq a => [a] -> Int
findCycleLength (x:as) = head [i | (i, a) <- zip [1..] as, x == a]
findCycleLength [] = error "findCycleLength of an empty list"

main :: IO ()
main = do
  Just input <- parse moves <$> readFile "input"
  let cycleLength = findCycleLength $ arrangements input
      solutionIndex = 1_000_000_000 `mod` cycleLength
  putStrLn $ arrangements input !! 0
  putStrLn $ arrangements input !! solutionIndex
