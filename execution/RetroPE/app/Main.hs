module Main where

import PEZ (retroGrover, retroShorp)

------------------------------------------------------------------------------

main :: IO ()
main = do
  retroShorp (Just 40) 21 1 -- should be fast: 15, 51, 83, 771; slower: 21, 35
  -- retroShorp (Just 42) 15 1
  -- mapM_ (retroGrover 5) [0..31]

-- Notes
-- For 21, 41 and 42 (as seeds) are lucky guesses; 40 'works'
-- For 15 and 51, 42 is not a lucky guess

------------------------------------------------------------------------------
