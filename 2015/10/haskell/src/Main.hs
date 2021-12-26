module Main (main) where

import Data.List (group, iterate')

input :: String
input = "1113222113"

lookAndSay :: String -> String
lookAndSay = foldMap (\g -> (show . length $ g) <> [head g]) . group

lookAndSayRecursively :: Int -> String -> Int
lookAndSayRecursively n = length . (!! n) . iterate' lookAndSay

main :: IO ()
main = do
  print . lookAndSayRecursively 40 $ input
  print . lookAndSayRecursively 50 $ input
