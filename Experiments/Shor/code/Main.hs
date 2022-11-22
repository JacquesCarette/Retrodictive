module Main where

import Control.Monad
import Text.Printf

import ShorOptimizedFourierBasis

main :: IO ()
main = do
  putStrLn (replicate 79 '_')
  putStrLn "Number to factor: (0 to exit)"
  m <- readLn
  when (m /= 0) $ do
    (f1,f2) <- factor m 10
    printf "Factors are %d and %d\n" f1 f2
    putStrLn (replicate 79 '_')
    main
  

  
