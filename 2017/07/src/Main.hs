module Main (main) where

import Au.Parser
import Data.Function (on)
import Data.List (elemIndices, nub, nubBy)
import Data.Maybe (listToMaybe, isNothing, fromJust)
import Data.Map.Strict (Map, fromList, (!), lookupGT)

data Node = Node
  { name' :: String
  , value' :: Integer
  , children' :: [String]
  } deriving (Eq, Show, Ord)

data Tree = Tree
  { name :: String
  , value :: Integer
  , children :: [Tree]
  } deriving (Eq, Show, Ord)

node :: Tokenizer Node
node = Node
  <$> alphabetical
  <*> (space >> parenthesised integer)
  <*> optional (word " -> " >> separatedBy (word ", ") alphabetical)

nodes :: String -> Maybe [Node]
nodes = parse (perLine node)

parent :: Node -> [Node] -> Maybe Node
parent child nodes = listToMaybe [n | n <- nodes, name' child `elem` children' n]

root :: [Node] -> Node
root nodes = head [n | n <- nodes, isNothing $ parent n nodes]

toTree :: Map String Node -> Node -> Tree
toTree nodes node =
  Tree
  { name = name' node
  , value = value' node
  , children = map (toTree nodes . (nodes !)) (children' node)
  }

balance :: Tree -> Integer
balance tree = value tree + (sum . map balance) (children tree)

balances :: Tree -> [Integer]
balances = map balance . children

childrenAreImbalanced :: Tree -> Bool
childrenAreImbalanced = (/= 1) . length . nub . balances

count :: Eq a => [a] -> a -> Int
count as a = length $ elemIndices a as

findImbalance :: Tree -> Integer
findImbalance tree =
  if childrenAreImbalanced tree && any childrenAreImbalanced (children tree)
    then findImbalance imbalancedChild
    else value imbalancedChild + imbalance
  where
    bs = balances tree
    balance2Child =
      fromList
        [ (count bs b, (b, c))
        | (b, c) <- nubBy ((==) `on` fst) $ zip bs (children tree)
        ]
    (imbalancedValue, imbalancedChild) = balance2Child ! 1
    correctValue = fst . snd . fromJust $ lookupGT 1 balance2Child
    imbalance = correctValue - imbalancedValue

main :: IO ()
main = do
  input <- readFile "input"
  let Just nodes' = nodes input
      nodes'' = fromList [(name' n, n) | n <- nodes']
      tree = toTree nodes'' $ root nodes'
  putStrLn $ name tree
  print . findImbalance $ tree
