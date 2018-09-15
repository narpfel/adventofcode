module Main (main) where

import Data.Composition
import qualified Data.IntMap.Strict as M

import Au.Parser

type Time = Int
type Position = Int
type Depth = Int

type Firewall = M.IntMap Depth

{-# INLINE position #-}
position :: Depth -> Time -> Position
position depth t
  | even d = m
  | otherwise = depth - 1 - m
    where
      (d, m) = t `divMod` (depth - 1)

{-# INLINE isCaught #-}
isCaught :: Depth -> Time -> Bool
isCaught = (== 0) .: position

{-# INLINE severity #-}
severity :: Firewall -> Time -> Int
severity fw delay =
  sum
    [ (pos + delay) * depth
    | (pos, depth) <- M.assocs fw
    , isCaught depth (pos + delay)
    ]

findDelay :: Firewall -> Time
findDelay fw = head . filter ((== 0) . severity fw) $ [0..]

firewall :: Tokenizer Firewall
firewall = M.fromList <$> perLine layer

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
