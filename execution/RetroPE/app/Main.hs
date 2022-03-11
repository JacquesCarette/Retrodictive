module Main where

import PEZ (retroGrover, retroShorp)

main :: IO ()
main = do
  retroShorp (Just 42) 51 1 -- should be fast: 15, 21, 51, 83, 771; slower: 21, 35
  -- mapM_ (retroGrover 5) [0..31]
