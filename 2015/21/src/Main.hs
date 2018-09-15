module Main where

data Fighter = Fighter
  { health :: Int
  , equipment :: Equipment
  } deriving Show

data Equipment = Equipment
  { cost :: Int
  , damage :: Int
  , armour :: Int
  } deriving Show

data Winner = Player | Boss deriving Show

(⊕) :: Equipment -> Equipment -> Equipment
x ⊕ y = Equipment
  { cost = cost x + cost y
  , damage = damage x + damage y
  , armour = armour x + armour y
  }

combinations :: [a] -> [(a, a)]
combinations (x:xs) = map ((,) x) xs ++ combinations xs
combinations _ = []

boss :: Fighter
boss = Fighter
  { health = 104
  , equipment = Equipment
    { cost = 0
    , damage = 8
    , armour = 1
    }
  }

attack :: Fighter -> Fighter -> Fighter
Fighter _ eqA `attack` Fighter hp eqD  = Fighter { health = hp - damageTaken, equipment = eqD }
  where
    damageTaken = max 1 $ damage eqA - armour eqD

hasLost :: Fighter -> Bool
hasLost = (<= 0) . health

fight :: Fighter -> Fighter -> Winner
fight p b =
  let b' = p `attack` b
   in if hasLost b'
         then Player
         else let p' = b' `attack` p
               in if hasLost p'
                     then Boss
                     else fight p' b'

playerWins :: Winner -> Bool
playerWins Player = True
playerWins _ = False

weapons :: [Equipment]
weapons =
  [ Equipment 8 4 0
  , Equipment 10 5 0
  , Equipment 25 6 0
  , Equipment 40 7 0
  , Equipment 74 8 0
  ]

armours :: [Equipment]
armours =
  [ Equipment 0 0 0
  , Equipment 13 0 1
  , Equipment 31 0 2
  , Equipment 53 0 3
  , Equipment 75 0 4
  , Equipment 102 0 5
  ]

rings :: [Equipment]
rings =
  [ Equipment 0 0 0
  , Equipment 0 0 0
  , Equipment 25 1 0
  , Equipment 50 2 0
  , Equipment 100 3 0
  , Equipment 20 0 1
  , Equipment 40 0 2
  , Equipment 80 0 3
  ]

allPlayers :: [Fighter]
allPlayers =
  [ Fighter { health = 100, equipment = foldr1 (⊕) [w, a, r1, r2] }
  | w <- weapons
  , a <- armours
  , (r1, r2) <- combinations rings
  ]

solve :: ([Int] -> Int) -> (Bool -> Bool) -> Int
solve costSelector p
  = costSelector
  . map (cost . equipment . fst)
  . filter (p . playerWins . uncurry fight)
  . zip allPlayers
  $ repeat boss

part1 :: Int
part1 = solve minimum id

part2 :: Int
part2 = solve maximum not

main :: IO ()
main = do
  print part1
  print part2
