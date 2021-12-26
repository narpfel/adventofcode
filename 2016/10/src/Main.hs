module Main (main) where

import Control.Lens hiding (Const)
import Control.Monad.State
import Data.Foldable (asum)
import Data.Functor (($>))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe (fromJust)

import Au.Parser

data Transaction
  = Const Int Target
  | Transfer Int Target Target

data Target
  = Bot Int
  | Output Int

data Factory = Factory
  { _bots :: IntMap IntSet
  , _outputs :: IntMap Int
  } deriving (Show)

makeLenses ''Factory

transaction :: Parser Char Transaction
transaction = const' <> transfer

const' :: Parser Char Transaction
const' = Const <$> (word "value " >> integer) <*> (word " goes to " >> bot)

transfer :: Parser Char Transaction
transfer = Transfer
  <$> (word "bot " >> integer)
  <*> (word " gives low to " >> target')
  <*> (word " and high to " >> target')

target' :: Parser Char Target
target' = bot <> output

bot :: Parser Char Target
bot = Bot <$> (word "bot " >> integer)

output :: Parser Char Target
output = Output <$> (word "output " >> integer)

executeTransaction :: Transaction -> State Factory (Maybe Int)
executeTransaction (Const value' (Bot bot')) =
  modify' (bots . at bot' . non mempty %~ IntSet.insert value') $> Nothing
executeTransaction (Const value' (Output output')) =
  modify' (outputs . at output' ?~ value') $> Nothing
executeTransaction (Transfer bot' lowTarget highTarget) = do
  values <- gets . view $ bots . at bot' . non mempty
  whenM (IntSet.size values == 2) $ do
    let [low', high'] = IntSet.toAscList values
    _ <- executeTransaction $ Const low' lowTarget
    _ <- executeTransaction $ Const high' highTarget
    whenM (low' == 17 && high' == 61) . pure . Just $ bot'

isSolution :: IntMap a -> Bool
isSolution m = and [i `IntMap.member` m | i <- [0..2]]

whenM :: Applicative f => Bool -> f (Maybe a) -> f (Maybe a)
whenM b ma = if b then ma else pure Nothing

main :: IO ()
main = do
  Just input <- parse (perLine transaction) <$> readFile "input"
  let (result, factory)
        = head
        . filter (isSolution . _outputs . snd)
        . iterate (runState (mapM executeTransaction input) . snd)
        $ (mempty, Factory mempty mempty)
  print . fromJust . asum $ result
  print . product . take 3 . IntMap.elems . _outputs $ factory
