module Main (main) where

import Control.Applicative (Alternative(some))
import Data.Functor (($>))
import Data.Maybe (mapMaybe)

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Au.Parser as Au
import Au.Parser hiding (Parser)

type Parser = Au.Parser Char

data Rule
  = Literal String
  | Compound [[Int]]
  deriving Show

rule :: Parser (Int, Rule)
rule = literalRule <> compoundRule

literalRule :: Parser (Int, Rule)
literalRule
  = (,)
  <$> (integer <* word ": ")
  <*> (Literal <$> between' "\"" "\"" (some $ no '"'))

compoundRule :: Parser (Int, Rule)
compoundRule
  = (,)
  <$> (integer <* word ": ")
  <*> (Compound <$> separatedBy (word " | ") (separatedBy (word " ") integer))

input :: Parser (Map Int Rule, [String])
input
  = (,)
  <$> (Map.fromList <$> perLine rule)
  <*> (word "\n\n" *> separatedBy' (word "\n") (some $ no '\n'))

buildParser :: Map Int Rule -> Int -> Parser ()
buildParser rules ruleName = go (rules Map.! ruleName) $> ()
  where
    go (Literal s) = word s $> ()
    go (Compound subrules) = choice . map (mapM_ (buildParser rules)) $ subrules

solve :: Map Int Rule -> [String] -> Int
solve rules = length . mapMaybe (parse rulesParser)
  where
    rulesParser = buildParser rules 0

main :: IO ()
main = do
  Just (rules, messages) <- parse input <$> readFile "input"
  let rulesPart2
        = Map.insert 11 (Compound [[42, 31], [42, 11, 31]])
        . Map.insert 8 (Compound [[42], [42, 8]])
        $ rules
  print . solve rules $ messages
  print . solve rulesPart2 $ messages
