module Main where

import Data.Char (isUpper)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Set (Set)
import qualified Data.Set as Set

data Step = Step
  { name :: Char
  , prerequisites :: Set Char
  } deriving (Ord, Eq)

fromString :: String -> Maybe Step
fromString [prerequisite', name'] = Just $ Step { name = name', prerequisites = Set.singleton prerequisite' }
fromString _ = Nothing

duration :: Char -> Int
duration = (+ 61) . subtract (fromEnum 'A') . fromEnum

parse :: String -> Maybe (Set Step)
parse = fmap Set.fromList . mapM (fromString . tail . filter isUpper) . lines

allValues :: Set Step -> Set Char
allValues
  = Set.unions
  . Set.map (\step -> name step `Set.insert` prerequisites step)

childNodes :: Set Step -> Set Char
childNodes = Set.map name

available :: Set Step -> Set Char
available steps = allValues steps Set.\\ childNodes steps

data Construction = Construction
  { workerCount :: Int
  , waiting :: Map Char (Set Char)
  , executing :: IntMap (Set Char)
  , done :: String
  , time :: Int
  } deriving Show

executeStep :: Construction -> Construction
executeStep = retire . queueExecution

queueExecution :: Construction -> Construction
queueExecution construction @ Construction { .. }
  = construction
    { waiting = waiting'
    , executing = executing'
    }
  where
    available' = Map.keysSet . Map.filter (`Set.isSubsetOf` Set.fromList done) $ waiting
    availableSlotCount = workerCount - length executing
    selected = Set.take availableSlotCount available'
    waiting' = Map.filterWithKey (\k _ -> not $ k `Set.member` selected) waiting
    executing'
      = IntMap.union executing
      . IntMap.fromList
      . Set.toAscList
      . Set.map (\c -> (duration c + time, [c]))
      $ selected

retire :: Construction -> Construction
retire construction @ Construction { .. }
  = construction
    { executing = executing'
    , done = done <> Set.toAscList retired
    , waiting = Map.map (Set.\\ retired) waiting
    , time = time'
    }
  where
    ((time', retired), executing') = IntMap.deleteFindMin executing

makeConstruction :: Set Step -> Construction
makeConstruction input =
  let noPrerequisites = Map.fromList . fmap (, Set.empty) . Set.toAscList . available $ input
      waiting'
        = Map.union noPrerequisites
        . Map.unionsWith Set.union
        . fmap (\Step { .. } -> Map.singleton name prerequisites)
        . Set.toAscList
        $ input
  in Construction
    { workerCount = 0
    , waiting = waiting'
    , executing = mempty
    , done = mempty
    , time = 0
    }

solve :: Int -> Construction -> Construction
solve workerCount'
  = until (\Construction { .. } -> Map.null waiting && IntMap.null executing) executeStep
  . (\c -> c { workerCount = workerCount' })

part1 :: Construction -> String
part1 = done . solve 1

part2 :: Construction -> Int
part2 = time . solve 5

main :: IO ()
main = do
  Just construction <- fmap makeConstruction . parse <$> readFile "input"
  putStrLn . part1 $ construction
  print . part2 $ construction
