module Main (main) where

import Control.Lens
import Control.Monad.State.Lazy
import Control.Applicative (liftA2, Alternative((<|>)))
import Data.Functor (($>))

data Fighter = Fighter
  { _health :: !Int
  , _mana :: !Int
  , _damage :: !Int
  } deriving (Show)

makeLenses ''Fighter

data Outcome = PlayerWins | EnemyWins deriving (Eq, Show)

newtype Shield = Shield Int deriving (Eq, Ord, Show)
newtype Poison = Poison Int deriving (Eq, Ord, Show)
newtype Recharge = Recharge Int deriving (Eq, Ord, Show)

data Move
  = Missile | Drain | ShieldMove | PoisonMove | RechargeMove
  deriving (Eq, Ord, Enum, Bounded, Show)

cost :: Move -> Int
cost = \case
  Missile -> 53
  Drain -> 73
  ShieldMove -> 113
  PoisonMove -> 173
  RechargeMove -> 229

data Fight = Fight
  { _player :: !Fighter
  , _enemy :: !Fighter
  , _shield :: !(Maybe Shield)
  , _poison :: !(Maybe Poison)
  , _recharge :: !(Maybe Recharge)
  , _manaSpent :: !Int
  } deriving (Show)

makeLenses ''Fight

shieldStrength :: Int
shieldStrength = 7

rechargeRate :: Int
rechargeRate = 101

poisonDamage :: Int
poisonDamage = 3

costs :: Int -> State Fight (Maybe Outcome)
costs amount = do
  player . mana -= amount
  manaSpent += amount
  hasManaLeft <- uses (player . mana) (>= 0)
  pure $ if not hasManaLeft then Just EnemyWins else Nothing

hit :: Int -> State Fight (Maybe Outcome)
hit amount = do
  enemy . health -= amount
  hp <- use $ enemy . health
  pure $ if hp <= 0 then Just PlayerWins else Nothing

hitPlayer :: Int -> State Fight (Maybe Outcome)
hitPlayer amount = do
  blockStrength <- maybe 0 (const shieldStrength) <$> use shield
  let amountIncludingShield = min amount . max 1 $ amount - blockStrength
  player . health -= amountIncludingShield
  hp <- use $ player . health
  pure $ if hp <= 0 then Just EnemyWins else Nothing

heal :: Int -> State Fight ()
heal amount = player . health += amount

applyEffects :: State Fight (Maybe Outcome)
applyEffects = do
  use shield >>= \case
    Just (Shield n) -> shield .= (Shield <$> n `sub` 1)
    Nothing -> pure ()
  use recharge >>= \case
    Just (Recharge n)
      -> (player . mana += rechargeRate)
      *> (recharge .= (Recharge <$> n `sub` 1))
    Nothing -> pure ()
  use poison >>= \case
    Just (Poison n)
      -> (poison .= (Poison <$> n `sub` 1))
      *> hit poisonDamage
    Nothing -> pure Nothing
  where
    n `sub` k
      | n - k < 0 = Nothing
      | otherwise = Just $ n - k

(<?>) :: (Applicative f, Alternative a) => f (a b) -> f (a b) -> f (a b)
(<?>) = liftA2 (<|>)

playerTurn :: Move -> State Fight (Maybe Outcome)
playerTurn move = applyEffects <?> costs (cost move) <?> case move of
  Missile -> hit 4
  Drain -> hit 2 <* heal 2
  ShieldMove -> (shield ?= Shield 6) $> Nothing
  PoisonMove -> (poison ?= Poison 5) $> Nothing
  RechargeMove -> (recharge ?= Recharge 4) $> Nothing

enemyTurn :: State Fight (Maybe Outcome)
enemyTurn = applyEffects <?> (hitPlayer =<< use (enemy . damage))

playRound :: Int -> Move -> State Fight (Maybe Outcome)
playRound additionalDamage move
  = hitPlayer additionalDamage
  <?> playerTurn move
  <?> enemyTurn

newFight :: Int -> Int -> Fight
newFight enemyHealth enemyStrength = Fight
  { _player = Fighter { _health = 50, _mana = 500, _damage = 0 }
  , _enemy = Fighter { _health = enemyHealth, _mana = 0, _damage = enemyStrength }
  , _shield = Nothing
  , _poison = Nothing
  , _recharge = Nothing
  , _manaSpent = 0
  }

input :: Fight
input = newFight 71 10

unfoldMap :: (a -> Maybe [a]) -> a -> [a]
unfoldMap f x
  = case f x of
      Nothing -> []
      Just xs -> xs <> concatMap (unfoldMap f) xs

solve :: Int -> Maybe Int -> Int
solve additionalDamage maxCost
  = minimum
  . map (_manaSpent . snd)
  . filter ((== Just PlayerWins) . fst)
  . unfoldMap (uncurry $ play additionalDamage maxCost)
  $ (Nothing, input)

play :: Int -> Maybe Int -> Maybe Outcome -> Fight -> Maybe [(Maybe Outcome, Fight)]
play _ _ (Just _) _ = Nothing
play additionalDamage maxCost _ fight
  | maybe False (_manaSpent fight >) maxCost = Nothing
  | otherwise = Just $ flip runState fight <$> plays
  where
    plays = map (playRound additionalDamage) (availableSpells fight)


availableSpells :: Fight -> [Move]
availableSpells fight
  = [Missile, Drain]
  <> [ShieldMove | fight & views shield (maybe True (<= Shield 1))]
  <> [RechargeMove | fight & views recharge (maybe True (<= Recharge 0))]
  <> [PoisonMove | fight & views poison (maybe True (<= Poison 0))]

part1 :: Int
part1 = solve 0 $ Just part2

part2 :: Int
part2 = solve 1 Nothing

main :: IO ()
main = do
  print part1
  print part2
