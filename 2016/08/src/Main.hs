module Main (main) where

import Control.Monad.State
import Data.Bool (bool)
import Data.List (transpose)

import Au.Parser

type Display = [[Bool]]

data Instruction
  = Rect Int Int
  | RotateRow Int Int
  | RotateColumn Int Int

instructions :: Parser Char [Instruction]
instructions = perLine . choice $ [rectP, rotateRowP, rotateColumnP]

rectP :: Parser Char Instruction
rectP = Rect <$> (word "rect " >> integer) <*> (word "x" >> integer)

rotateRowP :: Parser Char Instruction
rotateRowP = RotateRow <$> (word "rotate row y=" >> integer) <*> (word " by " >> integer)

rotateColumnP :: Parser Char Instruction
rotateColumnP = RotateColumn <$> (word "rotate column x=" >> integer) <*> (word " by " >> integer)

executeInstruction :: Instruction -> State Display ()
executeInstruction (Rect x y) = do
  display <- get
  put
    [ [ (x' < x && y' < y) || oldState
      | (x', oldState) <- zip [0..] row
      ]
    | (y', row) <- zip [0..] display
    ]
executeInstruction (RotateRow row amount)
  = modify' $ rotateRow row amount
executeInstruction (RotateColumn column amount)
  = modify' $ transpose . rotateRow column amount . transpose

rotate :: Int -> [a] -> [a]
rotate n xs = drop (l - n) xs ++ take (l - n) xs
  where
    l = length xs

rotateRow :: Int -> Int -> [[a]] -> [[a]]
rotateRow rowIndex amount xxs =
  [ if y == rowIndex then rotate amount row else row
  | y <- [0..]
  | row <- xxs
  ]

showDisplay :: Display -> String
showDisplay = unlines . (map . map) (bool ' ' '█')

main :: IO ()
main = do
  Just input <- parse instructions <$> readFile "input"
  let initialDisplay = replicate 6 . replicate 50 $ False
      finalDisplay = execState (mapM_ executeInstruction input) initialDisplay
  print . sum . (concatMap . map) fromEnum $ finalDisplay
  putStrLn . showDisplay $ finalDisplay
