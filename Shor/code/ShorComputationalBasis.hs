module ShorComputationalBasis where

import System.Random (randomRIO)

import GHC.Integer.GMP.Internals (powModInteger)

import Text.Printf (printf)

--

import PE

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Eventual entry point

-- Products of primes of the form 2^k+1 seem to work best:
-- first few are 3, 5, 17, 257, and 65537
factor :: Integer -> IO ()
factor m = do

  -- The period might be close to m/2 and we need at least m different
  -- values of x that have the same image. We might be able to use
  -- fewer bits but for now we will use log(m^2) bits

      let n = ceiling $ logBase 2 (fromInteger m * fromInteger m)
      a <- randomRIO (2,m-1)
      if gcd m a /= 1 
        then factor m -- lucky guess but try again to test circuit approach
        else do
          x <- randomRIO (0,m)
          let res = powModInteger a x m
          putStr "Running InvExpMod circuit symbolically with: "
          putStrLn (printf "n = %d; a = %d; m = %d; res = %d"
                    n a m res)
          runPE n a m res

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
