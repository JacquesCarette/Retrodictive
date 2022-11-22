module Shor where

import System.Random
import GHC.Integer.GMP.Internals
import Control.Monad
import Text.Printf

------------------------------------------------------------------------------

generateAndTest :: (Integer -> Integer) -> Integer -> Integer -> [Integer]
generateAndTest f range obs =
  map fst [ (x, f x) | x <- [0..range], f x == obs]

shorCore :: Integer -> IO (Integer,Integer)
shorCore n = 
  do x <- randomRIO (2, n - 1)
     printf "\tx = %d\n" x
     let f r = powModInteger x r n                       
     test <- randomRIO (0, (n * n))
     printf "\ttest = %d; obs = %d\n" test (f test)
     let (a : b : _) = generateAndTest f (n * n) (f test)
     let period = b - a                                  
     printf "\ta = %d, b = %d, period = %d\n" a b period
     let p1 = x ^ (period `div` 2) - 1                   
     let p2 = x ^ (period `div` 2) + 1                   
     return (gcd n p1, gcd n p2)                         
     
------------------------------------------------------------------------------

shorIter :: Integer -> Integer -> IO (Integer,Integer)
shorIter n iter =
  do printf "\n\nAttempting to factor %d (iteration %d)\n\n" n iter
     x <- randomRIO (2, n - 1)
     printf "Choose x = %d\n" x
     if gcd n x /= 1
       then do printf "Lucky guess!\n"
               return (gcd n x, 1)
       else do let f r = x ^ r `mod` n
               test <- randomRIO (0, n)
               printf "Second component fixed to %d\n" test
               let xs = generateAndTest f (n * n) test
               printf "Full list length = %d\n" (n * n)
               printf "Filtered list length = %d\n" (length xs)
               if (length xs < 2)
                 then do printf "Short list"
                         shorIter n (iter+1)
                 else do let a = head xs
                         let b = head (tail xs)
                         let period = b - a
                         printf "Period is %d\n" period
                         if (period `mod` 2 == 1)
                           then do printf "Unlucky: odd period"
                                   shorIter n (iter+1)
                           else do let p1 = x ^ (period `div` 2) - 1
                                   let p2 = x ^ (period `div` 2) + 1
                                   return (gcd n p1, gcd n p2)
     
shor :: Integer -> IO (Integer,Integer)
shor n = shorIter n 1

------------------------------------------------------------------------------
------------------------------------------------------------------------------