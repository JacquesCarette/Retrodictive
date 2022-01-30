{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Synthesis where

import Data.List
import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))
import Control.Monad.ST
import Data.STRef

import Debug.Trace as D
import Text.Printf

import Circuits

-- Synthsis algorithm from https://msoeken.github.io/papers/2016_rc_1.pdf

----------------------------------------------------------------------------------------
-- Simple helpers

-- negate bit i 

notI :: Int -> [Bool] -> [Bool]
notI i as = xs ++ (not y : ys) where (xs,y:ys) = splitAt i as

notIs :: [Bool] -> [Int] -> [Bool]
notIs = foldr notI

----------------------------------------------------------------------------------------
-- Algorithm

-- Core step of algorithm
-- Take two bit sequences x and y and return GToffoli gates to convert x to y
-- without disturbing any bit sequence that is lexicographically smaller than x

allBools :: Int -> [[Bool]]
allBools 0 = [[]]
allBools n = map (False :) bs ++ map (True :) bs
  where bs = allBools (n-1)

synthesisStep :: Value v => [Var s v] -> [Bool] -> [Bool] -> (OP s v, [Bool] -> [Bool])
synthesisStep vars xbools ybools
  | xbools == ybools = (S.empty, id)
  | otherwise = 
  let
    x0 = elemIndices False xbools
    x1 = elemIndices True  xbools
    y0 = elemIndices False ybools
    y1 = elemIndices True  ybools
    x0y1 = x0 `intersect` y1
    x1y0 = x1 `intersect` y0
    f01 xs = if and [ xs !! k | k <- x1] then notIs xs x0y1 else xs
    f10 xs = if and [ xs !! k | k <- x0] then notIs xs x1y0 else xs
    toff01 = [ GToffoli
               (replicate (length x1) True)
               [vars !! k | k <- x1]
               (vars !! i)
             | i <- x0y1
             ]
    toff10 = [ GToffoli
               (replicate (length x0) True)
               [vars !! k | k <- x0]
               (vars !! i)
             | i <- x1y0
             ]
  in (S.fromList (toff01 ++ toff10), f01 . f10)

-- Initialize; repeat synthesis; extract circuit

showF f = concat $ map (\b -> printf "%s\n" (show (b,f b))) (allBools 3)

synthesisLoop :: Value v =>
                 [Var s v] -> OP s v -> ([Bool] -> [Bool]) ->
                 [[Bool]] -> OP s v
synthesisLoop xs circ f [] = circ
synthesisLoop xs circ f (xbools : rest) = 
  let ybools = f xbools
      (circg,g) = synthesisStep xs xbools ybools
  in synthesisLoop xs (circg >< circ) (g . f) rest

synthesis :: Value v => Int -> [Var s v] -> ([Bool] -> [Bool]) -> OP s v
synthesis n xs f = synthesisLoop xs S.empty f (allBools n)

----------------------------------------------------------------------------------------
-- Some test cases

instance Enum String where
  toEnum = undefined
  fromEnum = undefined

instance Value String where
  zero =  undefined
  one =  undefined
  snot =  undefined
  sxor =  undefined
  sand =  undefined


test1 :: IO ()
test1 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  let op = synthesis 2 [x1,x0] (\[a,b] -> [a,a/=b])
  showOP op

test2 :: IO ()
test2 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  let op = synthesis 3 [x2,x1,x0] (\[a,b,c] -> [a,b,(a&&b)/=c])
  showOP op

test3 :: IO () 
test3 = putStrLn $ runST $ do
  x0 <- newSTRef "x1"
  x1 <- newSTRef "x2"
  x2 <- newSTRef "x3"
  let op = synthesis 3 [x0,x1,x2] f
  showOP op 
  where f [False,False,False] = [True,True,True]     -- 7
        f [False,False,True]  = [False,False,False]  -- 0
        f [False,True,False]  = [True,True,False]    -- 6
        f [False,True,True]   = [True,False,False]   -- 4
        f [True,False,False]  = [False,True,False]   -- 2 
        f [True,False,True]   = [False,False,True]   -- 1
        f [True,True,False]   = [False,True,True]    -- 3
        f [True,True,True]    = [True,False,True]    -- 5


----------------------------------------------------------------------------------------
