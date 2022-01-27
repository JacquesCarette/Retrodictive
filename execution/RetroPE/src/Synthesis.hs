{-# LANGUAGE MultiWayIf #-}

module Synthesis where

import Data.List
import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))
import Control.Monad.ST

import Circuits

{--

A fast symbolic transformation based algorithm for reversible logic synthesis

 Given 1-1 function f : n <-> n
 generate n vars
 C circuit over n vars = empty

 x = i
 y = f(i)

 X0 = { i | xi = 0 }
 X1 = { i | xi = 1 }

 Y0 = { i | yi = 0 }
 Y1 = { i | yi = 1 }

 Positions where x and y differ are:

   X1 intersect Y0 
   X0 intersect Y1

 Transform C

   Toffoli (X1,i) for i in X0 intersect Y1;
   Toffoli (Y1,i) for i in X1 intersect Y0;
   old C
 
--}

{--

Take two bit sequences x and y and return GToffoli gates to convert x to y
without disturbing any bit sequences that is lexicographically smaller than x

--}

instance Value Bool where
  zero = False
  one =  True
  snot b =  not b
  sand b1 b2 = b1 && b2
  sxor b1 b2 = b1 /= b2

notI :: Int -> [Bool] -> [Bool]
notI i as = xs ++ (not y : ys)
  where (xs,y:ys) = splitAt i as

notIs :: [Bool] -> [Int] -> [Bool]
notIs = foldr notI

synthesisStep :: Value v => [Var s v] -> [Bool] -> [Bool] -> (OP s v, [Bool] -> [Bool])
synthesisStep vars xbools ybools = 
  let
    x0 = elemIndices False xbools
    x1 = elemIndices True  xbools
    y0 = elemIndices False ybools
    y1 = elemIndices True  ybools
    x0y1 = x0 `intersect` y1
    x1y0 = x1 `intersect` y0
    toff01 = [ GToffoli
               (replicate (length x1) True)
               [vars !! k | k <- x1]
               (vars !! i)
             | i <- x0y1
             ]
    toff10 = [ GToffoli
               (replicate (length y1) True)
               [vars !! k | k <- y1]
               (vars !! i)
             | i <- x1y0
             ]
    f01 xs = if and [xs !! k | k <- x1]
             then notIs xs x0y1
             else xs
    f10 xs = if and [xs !! k | k <- y1]
             then notIs xs x1y0
             else xs
  in (S.fromList (toff01 ++ toff10), f10 . f01)

-- Not quite probably; needs testing
-- give names to vars; or perhaps just interp
-- and check it is equivalent to original function

synthesis :: Int -> ([Bool] -> [Bool]) -> ST s (OP s Bool)
synthesis n f = undefined

-- 

test1 :: IO ()
test1 = putStrLn $ runST $ do
  op <- synthesis 2 (\[a,b] -> [a,a/=b])
  showOP op

test2 :: IO ()
test2 = putStrLn $ runST $ do
  op <- synthesis 3 (\[a,b,c] -> [a,b,(a&&b)/=c])
  showOP op

test3 :: IO ()
test3 = putStrLn $ runST $ do
  op <- synthesis 12 f
  -- showOP op
  return ("length = " ++ show (S.length op))
  where f xs = let (as,bs) = splitAt 7 xs
                   (cs,ds) = elevenPowerMod21 as bs
               in cs ++ ds

test4 :: IO () 
test4 = putStrLn $ runST $ do
  op <- synthesis 3 f
  showOP op
  where f [False,False,False] = [True,True,True]
        f [False,False,True]  = [False,False,False]
        f [False,True,False]  = [True,True,False]
        f [False,True,True]   = [True,False,False]
        f [True,False,False]  = [False,True,False]
        f [True,False,True]   = [False,False,True]
        f [True,True,False]   = [False,True,True]
        f [True,True,True]    = [True,False,True]


elevenPowerMod21 :: [Bool] -> [Bool] -> ([Bool],[Bool])
elevenPowerMod21 xs hs@[h4,h3,h2,h1,h0] =
  if | xInt `elem` [0,6..126]  -> (xs, [h4,h3,h2,h1,not h0])
     | xInt `elem` [1,7..127]  -> (xs, [h4,not h3,h2,not h1,not h0])
     | xInt `elem` [2,8..122]  -> (xs, [not h4,h3,h2,h1,h0])
     | xInt `elem` [3,9..123]  -> (xs, [h4,not h3,h2,h1,h0])
     | xInt `elem` [4,10..124] -> (xs, [h4,h3,not h2,h1,h0])
     | xInt `elem` [5,11..125] -> (xs, [h4,h3,h2,not h1,h0])
  where xInt = toInt xs

