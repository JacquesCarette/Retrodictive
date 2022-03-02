module Main where

import PEZ (retroGrover, retroShor)

main :: IO ()
main = do
  retroShor 51 -- should be fast: 15, 21, 51, 83, 771; slower: 21, 35
  -- mapM_ (retroGrover 5) [0..31]
