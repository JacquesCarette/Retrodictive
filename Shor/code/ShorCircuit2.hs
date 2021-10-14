{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}

-- Following:
-- Quantum Networks for Elementary Arithmetic Operations
-- Vlatko Vedral∗, Adriano Barenco and Artur Ekert

module Shor where

import Data.Char
import GHC.Integer.GMP.Internals
import Data.Vector (Vector, fromList, toList, (!), (//))
import qualified Data.Vector as V 
import Control.Monad.ST
import Data.STRef
import Data.Array.ST
import qualified Control.Category as Cat
import Control.Arrow
  
import Text.Printf
import Test.QuickCheck
import Control.Exception.Assert

import qualified Debug.Trace

-- Toggle 

debug = False
--debug = True

trace :: String -> a -> a
trace s a = if debug then Debug.Trace.trace s a else a

------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Syntax

type Var s = STRef s (String,Bool)

data OP s = 
    ID
  | CX (Var s) (Var s)
  | CCX (Var s) (Var s) (Var s)
  | (:.:) (OP s) (OP s)
{--
    NCX :: OP (Bool,Bool) (Bool,Bool)
    CCX :: OP (Bool,Bool,Bool) (Bool,Bool,Bool)
    COP :: OP Bool (OP a b)
    NCOP :: OP Bool (OP a b)
    SWAP :: OP (a,b) (b,a)
    ALLOC :: a -> OP () a
    DEALLOC :: OP a ()
    LOOP :: [a] -> OP a b -> OP [a] [b]
    (:*:) :: OP a b -> OP c d -> OP (a,c) (b,d)
--}

invert :: OP s -> OP s
invert ID = ID
invert (CX a b) = CX a b
invert (CCX a b c) = CCX a b c
invert (op1 :.: op2) = invert op2 :.: invert op1
{--
invert CCX = CCX
invert (op1 :*: op2)    = invert op1 :*: invert op2
invert (NCX i j)        = NCX i j
invert (COP i op)       = COP i (invert op)
invert (NCOP i op)      = NCOP i (invert op)
invert (SWAP i j)       = SWAP i j
invert (ALLOC i)        = DEALLOC i
invert (DEALLOC i)      = ALLOC i
invert (LOOP indices f) = LOOP (reverse indices) (\k -> invert (f k))
--}
       
-- count number of primitive operations

size :: OP s -> Int
size ID                = 1
size (CX _ _)          = 1
size (CCX _ _ _)       = 1
size (op1 :.: op2)     = size op1 + size op2
{--
size (op1 :*: op2)    = size op1 + size op2
size (NCX i j)        = 1
size (COP i op)       = size op
size (NCOP i op)      = size op
size (SWAP i j)       = 1
size (ALLOC i)        = 1
size (DEALLOC i)      = 1
size (LOOP indices f) = size (f 0) * length indices
--}

------------------------------------------------------------------------------
-- Monadic interpreter

interpM :: OP s -> ST s ()
interpM ID = return () 
interpM (CX a b) = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  writeSTRef b (sb, if va then not vb else vb)
interpM (CCX a b c) = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  (sc,vc) <- readSTRef c
  writeSTRef c (sc, if va && vb then not vc else vc)
interpM (op1 :.: op2) =
  do interpM op1 ; interpM op2
{--
interpM CCX r = do
  (a,b,c) <- readSTRef r
  let (a',b',c') = if a && b then (a,b, not c) else (a,b,c)
  writeSTRef r (a',b',c')
  return (a',b',c')
    NCX  :: OP (Bool,Bool) (Bool,Bool)
    COP :: OP Bool (OP a b)
    NCOP :: OP Bool (OP a b)
    SWAP :: OP (a,b) (b,a)
    ALLOC :: a -> OP () a
    DEALLOC :: OP a ()
    LOOP :: [a] -> OP a b -> OP [a] [b]
    (:.:) :: OP a b -> OP b c -> OP a c
    (:*:) :: OP a b -> OP c d -> OP (a,c) (b,d)
--}
 
showM :: OP s -> String -> ST s String
showM ID d = return d
showM (CX a b) d = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  return (printf "%sCX (%s,%s) (%s,%s)" d sa (show va) sb (show vb))
showM (CCX a b c) d = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  (sc,vc) <- readSTRef c
  return (printf "%sCCX (%s,%s) (%s,%s) (%s,%s)" d sa (show va) sb (show vb) sc (show vc))
showM (op1 :.: op2) d = do
  s1 <- showM op1 d
  s2 <- showM op2 d
  return (printf "%s :.:\n%s" s1 s2)

------------------------------------------------------------------------------
-- Helpers

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

toInt :: [Bool] -> Integer
toInt bs = foldr (\b n -> toInteger (fromEnum b) + 2*n) 0 bs

var :: String -> Bool -> ST s (Var s)
var s v = newSTRef (s,v)

vars :: String -> [Bool] -> ST s [Var s]
vars s vs = mapM (\ (v,i) -> newSTRef (s ++ show i, v))
                 (zip vs [0..(length vs)])

-- Actual circuits 

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b =
  CX a b :.: CX c b

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' =
  CCX a b c' :.:
  CX a b :.:
  CCX c b c'

--           n    [a0,a1,...an][b0,b1,...bn]
makeAdder :: Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder n as bs =
  do cs <- vars "c" (replicate (n+1) False)
     return (loop as bs cs)
       where loop [a] [b] [c,c'] =
               carryOP c a b c' :.:
               CX a b :.:
               sumOP c a b
             loop (a:as) (b:bs) (c:c':cs) =
               carryOP c a b c' :.:
               loop as bs (c':cs) :.:
               invert (carryOP c a b c') :.:
               sumOP c a b

--              n      m       [a0,a1,...an] [b0,b1,...bn]
makeAdderMod :: Int -> Integer -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdderMod n m as bs = 
  do ms <- vars "m" (fromInt n m)
     t <- var "t" False
     adder1 <- makeAdder n as bs
     adder2 <- makeAdder n ms bs
     return (adder1 :.: invert adder2) -- TO BE CTD
  
------------------------------------------------------------------------------
-- Testing

test :: (String,Bool)
test = runST $
  do a <- var "a" False
     b <- var "b" True
     c <- var "c" False
     interpM (sumOP a b c)
     readSTRef c

test2 :: (String,Bool)
test2 = runST $
  do a <- var "a" False
     b <- var "b" True
     c <- var "c" False
     interpM (invert (sumOP a b c))
     readSTRef c

test3 :: [(String,Bool)]
test3 = runST $
  do as <- vars "a" [False, True, False]
     bs <- vars "b" [False, False, True]
     adderOP <- makeAdder 3 as bs
     interpM adderOP
     mapM readSTRef bs

test4 :: IO ()
test4 = printf "%s\n" $ runST $
  do as <- vars "a" [False, True, False]
     bs <- vars "b" [False, False, True]
     adderOP <- makeAdder 3 as bs
     showM adderOP ""

------------------------------------------------------------------------------
------------------------------------------------------------------------------
