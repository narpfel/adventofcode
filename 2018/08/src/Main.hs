module Main (main) where

import Au.Parser

data Tree = Tree
  { children :: [Tree]
  , metadata :: [Integer]
  }

tree :: Parser Integer Tree
tree = do
  childrenCount <- anything
  metadataCount <- anything
  Tree <$> exactly childrenCount tree <*> exactly metadataCount anything

part1 :: Tree -> Integer
part1 Tree { .. } = sum metadata + sum (part1 <$> children)

(!?) :: [a] -> Int -> Maybe a
xs !? i
  | i < 0 || i >= length xs = Nothing
  | otherwise = Just $ xs !! i

part2 :: Tree -> Integer
part2 Tree { .. }
  | null children = sum metadata
  | otherwise
    = sum
    . fmap (maybe 0 part2 . (children !?) . subtract 1 . fromIntegral)
    $ metadata

main :: IO ()
main = do
  Just input <- parse tree . fmap read . words <$> readFile "input"
  print . part1 $ input
  print . part2 $ input
