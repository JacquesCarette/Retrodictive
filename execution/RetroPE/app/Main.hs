module Main where

import PEZ (retroGrover)

main :: IO ()
main = do
  mapM_ (retroGrover 5) [0..31]
