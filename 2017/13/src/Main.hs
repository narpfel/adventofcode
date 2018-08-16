module Main where

import qualified Data.Map.Strict as M

import Au.Parser

type Time = Int
type Position = Int

newtype Firewall = Firewall [Layer] deriving Show

newtype Layer = Layer { depth :: Int } deriving Show

position :: Layer -> Time -> Position
position layer t
  | even $ t `div` l = t `mod` l
  | otherwise = l - (t `mod` l)
    where
      l = depth layer - 1

isCaught :: Layer -> Time -> Bool
isCaught l t = position l t == 0

severity :: Time -> Firewall -> Int
severity delay (Firewall layers) =
  sum
    [ p * depth l
    | (l, p) <- zip layers [delay..]
    , isCaught l p
    ]

firewall :: Tokenizer Firewall
firewall = do
  layers <- M.fromList <$> perLine layer
  let keys = M.keys layers
      maxKey = maximum keys
  return . Firewall $
    [ l
    | p <- [0..maxKey]
    , let l = M.findWithDefault (Layer 0) p layers
    ]

layer :: Tokenizer (Position, Layer)
layer =
  (,)
  <$> integer
  <*> (word ": " >> (Layer <$> integer))

findDelay :: Firewall -> Time
findDelay f = go 0
  where
    go t = if severity t f == 0
              then t
              else go $ t + 1

main :: IO ()
main = do
  Just f <- parse firewall <$> readFile "input"
  print . severity 0 $ f
  print . findDelay $ f

