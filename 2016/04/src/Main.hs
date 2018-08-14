module Main where

import Control.Arrow ((&&&))
import Control.Applicative (some)
import Control.Monad (guard)
import Data.Char (ord, chr)
import Data.List (sort, sortBy, group, find)
import Data.Maybe (mapMaybe, fromJust)

import Au.Parser

encryptedName :: Tokenizer [String]
encryptedName = some (alphabetical <* char '-')

sectorID :: Tokenizer Int
sectorID = integer

checksum :: Tokenizer String
checksum = char '[' *> alphabetical <* char ']'

room :: Tokenizer (Int, String)
room = do
    name <- encryptedName
    s <- sectorID
    cs <- checksum
    _ <- optional (word "\n")
    let cmp (l, c) (l', c') =
          case compare l' l of
            EQ -> compare c c'
            o -> o
        letterCounts = map (length &&& head) . group . sort . concat $ name
        expectedChecksum = map snd . take 5 . sortBy cmp $ letterCounts
    guard (expectedChecksum == cs)
    return (s, unwords . map (decrypt s) $ name)


decrypt :: Int -> String -> String
decrypt k = map (rotateChar k)

rotateChar :: Int -> Char -> Char
rotateChar k c = chr $ (ord c - ord 'a' + k) `mod` 26 + ord 'a'

main :: IO ()
main = do
    rooms <- mapMaybe (parse room) . lines <$> readFile "input"
    print . sum . map fst $ rooms
    print . fst . fromJust . find ((== "northpole object storage") . snd) $ rooms
