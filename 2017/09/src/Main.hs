module Main (main) where

import Control.Applicative ((<|>), many)
import Data.Maybe (catMaybes)

import Au.Parser

data Stream = Group [Stream]
            | Garbage String
            deriving (Show, Eq, Ord)

group :: Tokenizer Stream
group = Group <$> (braced . optional $ separatedBy (word ",") (group <|> garbage))

garbage :: Tokenizer Stream
garbage = Garbage . catMaybes <$> between' "<" ">" (many garbageContent)
  where
    garbageContent = (char '!' >> anything >> pure Nothing) <|> (Just <$> no '>')

score :: Stream -> Integer
score = go 1
  where
    go :: Integer -> Stream -> Integer
    go n (Group ss) = n + sum (map (go (n + 1)) ss)
    go _ (Garbage _) = 0

countGarbageChars :: Stream -> Int
countGarbageChars (Group ss) = sum $ map countGarbageChars ss
countGarbageChars (Garbage cs) = length cs

main :: IO ()
main = do
  Just input <- parse group . head . lines <$> readFile "input"
  print . score $ input
  print . countGarbageChars $ input
