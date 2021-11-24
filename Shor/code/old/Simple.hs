{-# LANGUAGE TemplateHaskell #-}

module Simple where

import GHC.Integer.GMP.Internals
import System.Random
import Test.QuickCheck

-- Compute a^x mod m for fixed 'a' and 'm'
-- Do it by looking at bits of x
-- m > 1

------------------------------------------------------------------------------
-- Circuits

-- Preprocessing
-- Given 'a' and 'm'
-- choose random 'x'
-- and compute the following:

as :: Integer -> [Bool]
as a = fromInt a
       
doublemods :: Integer -> Integer -> [[Bool]]
doublemods a m = fromInt a : doublemods ((2*a) `mod` m) m

sqmods :: Integer -> Integer -> [[Bool]]
sqmods a m = fromInt a : sqmods ((a * a) `mod` m) m

obs :: Integer -> Integer -> Integer -> [Bool]
obs a x m = fromInt $ powModInteger a x m

------------------------------------------------------------------------------
-- Now we know
-- m, as, doublemods, sqmods, and obs
-- goal is to find xs such that
-- (as ^ xs) `mod` m = obs

-- do addmod with bits; merge all following in one giant loop

-- (a + xs) `mod` m
addmod :: [Bool] -> [Bool] -> Integer -> [Bool]
addmod as xs m = fromInt $ (toInt as + toInt xs) `mod` m

-- (a * xs) `mod` m
mulmod :: Integer -> [Bool] -> Integer -> [Bool]
mulmod a xs m = mulmodIter (doublemods a m) xs m (fromInt 0)

mulmodIter :: [[Bool]] -> [Bool] -> Integer -> [Bool] -> [Bool]
mulmodIter as [] m res = res
mulmodIter (a:as) (x:xs) m res
  | x         = mulmodIter as xs m (addmod a res m)
  | otherwise = mulmodIter as xs m res

-- (a ^ x) `mod` m
expmod :: Integer -> Integer -> Integer -> [Bool]
expmod a x m = expmodIter (sqmods a m) (fromInt x) m (fromInt 1)

expmodIter :: [[Bool]] -> [Bool] -> Integer -> [Bool] -> [Bool]
expmodIter as [] m res = res
expmodIter (a:as) (x:xs) m res
  | x         = expmodIter as xs m (mulmod (toInt a) res m)
  | otherwise = expmodIter as xs m res


{--

Focus on expmodIter:

* as                       known
* xs                       unknown
* m                        known
* res                      known
* (expmodIter as xs m res) known

--}



















------------------------------------------------------------------------------
-- Testing

-- fromInt 19 ==> [1,1,0,0,1]
fromInt :: Integer -> [Bool]
fromInt 0 = []
fromInt n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : fromInt q

toInt :: [Bool] -> Integer
toInt bs = foldr (\ b n -> toInteger (fromEnum b) + 2*n) 0 bs

{--

expmodIter :: [Integer] -> [Bool] -> Integer -> Integer
expmodIter as [] m = 1
expmodIter (a:as) (x:xs) m
  | x         = (a * expmodIter as xs m) `mod` m
  | otherwise = expmodIter as xs m

expmod :: Integer -> [Bool]           -> Integer -> Integer
expmod a xs m = loop a xs
  where
    loop a []     = 1 `mod` m
    loop a (x:xs) =
      let r = loop ((a*a) `mod` m) xs
      in if x
         then (a * r) `mod` m
         else r

--              a          x          n
periodFinder :: Integer -> Integer -> Integer -> Integer 
periodFinder a x n =
  let fx = expmod a (fromInt x) n
  -- now we have:
  -- expmod a UNKNOWN m = fx
  -- find UNKNOWN
  -- run with symbolic xs
  in 0
  


generateAndTest :: (Integer -> Integer) -> Integer -> Integer -> [Integer]
generateAndTest f range obs =
  map fst [ (x, f x) | x <- [0..range], f x == obs]
  
shorIO :: Integer -> IO (Integer,Integer)
shorIO n =
  do x <- randomRIO (2, n - 1)
     let f r = expmod x (fromInt r) n                       
     test <- randomRIO (0, (n * n))
     let (a : b : _) = generateAndTest f (n * n) (f test)
     let period = b - a                                  
     let p1 = x ^ (period `div` 2) - 1                   
     let p2 = x ^ (period `div` 2) + 1                   
     return (gcd n p1, gcd n p2)                         
     
------------------------------------------------------------------------------
-- Testing

expmodGen :: Gen (Integer,Integer,Integer)
expmodGen =
  do n <- chooseInt (1,100)
     a <- chooseInteger (0,2^n-1)
     x <- chooseInteger (0,2^n-1)
     m <- chooseInteger (1,2^n-1)
     return (a,x,m)

prop_expmod :: Property
prop_expmod = forAll expmodGen $ \ (a,x,m) ->
  let actual = expmod a (fromInt x) m
      expected = powModInteger a x m
  in actual === expected

------------------------------------------------------------------------------
-- Run all tests

return []                  -- ... weird TH hack !!!
test = $quickCheckAll

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

--}
