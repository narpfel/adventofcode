module Main (main) where

import Au.Parser

type Time = Int
type Position = Int
type Depth = Int

type Firewall = [Maybe Int]

{-# INLINE position #-}
position :: Depth -> Time -> Position
position depth t
  | even d = m
  | otherwise = depth - 1 - m
    where
      (d, m) = t `divMod` (depth - 1)

{-# INLINE isCaught #-}
isCaught :: Depth -> Time -> Bool
isCaught d t = position d t == 0

{-# INLINE severity #-}
severity :: Firewall -> Time -> Int
severity fw delay =
  sum $ severities fw delay

severities :: Firewall -> Time -> [Int]
severities fw delay =
  [ (pos + delay) * depth
  | (pos, Just depth) <- zip [0..] fw
  , isCaught depth (pos + delay)
  ]

findDelay :: Firewall -> Time
findDelay fw = head . filter (null . severities fw) $ [0..]

firewall :: Tokenizer Firewall
firewall = go [] <$> perLine layer
  where
    go :: [Maybe Int] -> [(Position, Depth)] -> [Maybe Int]
    go xs ((p, d):rest)
      | length xs == p = go (xs ++ [Just d]) rest
      | otherwise  = go (xs ++ [Nothing]) ((p, d):rest)
    go xs [] = xs

layer :: Tokenizer (Position, Depth)
layer =
  (,)
  <$> integer
  <*> (word ": " >> integer)

main :: IO ()
main = do
  Just f <- parse firewall <$> readFile "input"
  print . severity f $ 0
  print . findDelay $ f
