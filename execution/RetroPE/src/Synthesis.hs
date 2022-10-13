{-# LANGUAGE ViewPatterns #-}

module Synthesis where

import Data.List (elemIndices, intersect)
import qualified Data.Sequence as S
import Data.Sequence ((><))

import GToffoli (GToffoli(GToffoli))
import Circuits (OP)
import Value (fromInt)
import Variable (Var)

------------------------------------------------------------------------------
-- Synthesis algorithm from https://msoeken.github.io/papers/2016_rc_1.pdf

-- Simple helpers

viewL :: [a] -> ([a],a)
viewL xs = (init xs, last xs)

-- negate bit i 

notI :: Int -> [Bool] -> [Bool]
notI i as = xs ++ (not y : ys) where (xs,y:ys) = splitAt i as

notIs :: [Bool] -> [Int] -> [Bool]
notIs = foldr notI

allBools :: Int -> [[Bool]]
allBools 0 = [[]]
allBools n = map (False :) bs ++ map (True :) bs
  where bs = allBools (n-1)

------------------------------------------------------------------------------
-- Algorithm

-- Core step of algorithm
-- Take two bit sequences x and y and return GToffoli gates to convert x to y
-- without disturbing any bit sequence that is lexicographically smaller than x

synthesisStep :: [br] -> [Bool] -> [Bool] -> (OP br, [Bool] -> [Bool])
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

synthesisLoop :: [br] -> OP br -> ([Bool] -> [Bool]) ->
                 [[Bool]] -> OP br 
synthesisLoop xs circ f [] = circ
synthesisLoop xs circ f (xbools : rest) = 
  let ybools = f xbools
      (circg,g) = synthesisStep xs xbools ybools
  in synthesisLoop xs (circg >< circ) (g . f) rest

synthesis :: Int -> [br] -> ([Bool] -> [Bool]) -> OP br 
synthesis n xs f = synthesisLoop xs S.empty f (allBools n)

------------------------------------------------------------------------------
-- Generate all balanced function (2^n -> 2)

subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (a:as) = map (a :) ss ++ ss
  where ss = subsets as

allFuns :: Int -> [[Bool] -> Bool]
allFuns n = [(`elem` ts) | ts <- maptoT ]
  where maptoT = subsets (allBools n)

allBalancedFuns :: Int -> [[Bool] -> Bool]
allBalancedFuns n = [(`elem` ts) | ts <- maptoT, length ts == bigN `div` 2 ]
  where bigN = 2 ^ n
        maptoT = subsets (allBools n)

{--
number of balanced functions

n=0     1
n=1     2
n=2     6
n=3    70
n=4 12870

--}
------------------------------------------------------------------------------
-- Special synthesis for Grover functions that are guaranteed to have
-- just one entry u such that f(u) = 1

synthesisGrover :: Int -> [br] -> Integer -> OP br
synthesisGrover n (viewL -> (xs,y)) u =
  S.singleton $ GToffoli (fromInt n u) xs y
  

------------------------------------------------------------------------------
