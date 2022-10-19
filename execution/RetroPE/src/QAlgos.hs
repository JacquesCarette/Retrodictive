{-# LANGUAGE ViewPatterns #-}

module QAlgos where

import Data.Sequence (fromList)

import Numeric (readHex)
import Text.Printf (printf)

import GToffoli (cx, ccx, cncx)
import Circuits (OP)
import Synthesis (viewL,synthesis,synthesisGrover)
import BoolUtils (toInt)

------------------------------------------------------------------------------
-- Generic quantum oracle construction

uf :: ([Bool] -> Bool) -> ([Bool] -> [Bool])
uf f (viewL -> (xs,y)) = xs ++ [f xs /= y]

----------------------------------------------------------------------------------------
-- Quantum algorithms

-- Deutsch

deutschId, deutschNot, deutsch0, deutsch1 :: [Bool] -> [Bool]
deutschId [x,y]  = [x,y /= x]
deutschNot [x,y] = [x,y /= not x]
deutsch0 [x,y]   = [x,y]
deutsch1 [x,y]   = [x,not y]

deutschCircuit :: ([Bool] -> [Bool]) -> br -> br -> OP br
deutschCircuit f x y = synthesis 2 [x, y] f

------------------------------------------------------------------------------
-- Deutsch Jozsa

deutschJozsaConstant0, deutschJozsaConstant1 :: [Bool] -> [Bool]
deutschJozsaBal1, deutschJozsaBal2, deutschJozsaBal3, deutschJozsaBal4 :: [Bool] -> [Bool]
-- f(x) = 0
deutschJozsaConstant0 = uf (const False)
-- f(x) = 1
deutschJozsaConstant1 = uf (const True)
-- f(x0x1x2..) = x0
deutschJozsaBal1 = uf head
-- f(x0x1x2..) = xor(x0,x1,x2...)
deutschJozsaBal2 = uf (foldr (/=) False)
-- Example 1 from https://ajc.maths.uq.edu.au/pdf/29/ajc_v29_p231.pdf
-- n=6; output in hex 04511b5e37e23e6d
deutschJozsaBal3 = uf f
  where shex = "04511b5e37e23e6d"
        h2Int :: Char -> Int
        h2Int c = fst (head (readHex [c]))
        h2Str :: Char -> String
        h2Str c = printf "%04b" (h2Int c)
        sbin :: [Bool]
        sbin = map (== '0') $ concatMap h2Str shex
        f xs = sbin !! fromInteger (toInt xs)
-- f(x0x1x2..) = xn
deutschJozsaBal4 = uf last

deutschJozsaCircuit :: Int -> ([Bool] -> [Bool]) -> [br] -> OP br
deutschJozsaCircuit n f l = synthesis (n+1) l f

------------------------------------------------------------------------------
-- Bernstein-Vazirani
-- n=8, hidden=92 [00111010]

retroBernsteinVaziraniCircuit :: [ br ] -> br -> OP br
retroBernsteinVaziraniCircuit xs y =
  fromList [ cx (xs !! 1) y
           , cx (xs !! 3) y
           , cx (xs !! 4) y
           , cx (xs !! 5) y
           ]

------------------------------------------------------------------------------
-- Simon
-- n=2, a=3

simonCircuit23 :: [ br ] -> [ br ] -> OP br
simonCircuit23 xs as =
  fromList [ cx (head xs) (head as)
           , cx (head xs) (as !! 1)
           , cx (xs !! 1) (head as)
           , cx (xs !! 1) (as !! 1)
           ]

------------------------------------------------------------------------------
-- Grover

groverCirc :: br -> [br] -> Int -> Integer -> OP br
groverCirc y xs n w = synthesisGrover (n+1) (xs ++ [y]) w

------------------------------------------------------------------------------
-- Small manually optimized Shor 21 from the IBM paper

shor21 :: br -> br -> br -> br -> br -> OP br
shor21 c0 c1 c2 q0 q1 = fromList
      [ cx c2 q1
      , cx c1 q1
      , cx q1 q0
      , ccx c1 q0 q1
      , cx q1 q0
      , cncx c0 q1 q0
      , cx q1 q0
      , ccx c0 q0 q1
      , cx q1 q0
      ]

