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

data OP s = 
    ID
  | CX (STRef s Bool) (STRef s Bool)
  | CCX (STRef s Bool) (STRef s Bool) (STRef s Bool)
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

{--
instance Show OP where
  show op = showH "" op
    where
      showH d (CX i j)        = printf "%sCX %d %d" d i j
      showH d (NCX i j)       = printf "%sNCX %d %d" d i j
      showH d (CCX i j k)     = printf "%sCCX %d %d %d" d i j k
      showH d (COP i op)      = printf "%sCOP %d (\n%s)" d i (showH ("  " ++ d) op)
      showH d (NCOP i op)     = printf "%sNCOP %d (\n%s)" d i (showH ("  " ++ d) op)
      showH d (SWAP i j)      = printf "%sSWAP %d %d" d i j
      showH d (op1 :.: op2)   = printf "%s :.:\n%s" (showH d op1) (showH d op2)
      showH d (ALLOC i)       = printf "%sALLOC %d" d i
      showH d (DEALLOC i)     = printf "%sDEALLOC %d" d i
      showH d (LOOP [] f)     = printf ""
      showH d (LOOP [i] f)    = printf "%s" (showH d (f i))
      showH d (LOOP (i:is) f) = printf "%s\n%s" (showH d (f i)) (showH d (LOOP is f))
--}

invert :: OP s -> OP s
invert ID = ID
invert (CX ra rb) = CX ra rb
invert (CCX ra rb rc) = CCX ra rb rc
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
size ID = 1
size (CX _ _)          = 1
{--
size CCX         = 1
size (op1 :.: op2)    = size op1 + size op2
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
interpM (CX ra rb) = do
  a <- readSTRef ra
  b <- readSTRef rb
  writeSTRef rb (if a then not b else b)
interpM (CCX ra rb rc) = do
  a <- readSTRef ra
  b <- readSTRef rb
  c <- readSTRef rc
  writeSTRef rc (if a && b then not c else c)
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

------------------------------------------------------------------------------
-- Actual circuits

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

sumOP :: STRef s Bool -> STRef s Bool -> STRef s Bool -> OP s
sumOP rc ra rb =
  CX ra rb :.: CX rc rb

carryOP :: STRef s Bool -> STRef s Bool -> STRef s Bool -> STRef s Bool -> OP s
carryOP rc ra rb rc' =
  CCX ra rb rc' :.:
  CX ra rb :.:
  CCX rc rb rc'

--           n      [a0,a1,...an]       [b0,b1,...bn]
makeAdder :: Int -> [ STRef s Bool ] -> [ STRef s Bool ] -> ST s (OP s)
makeAdder n as bs =
  do cs <- mapM newSTRef (replicate (n+1) False)
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

--              n      m          [a0,a1,...an]       [b0,b1,...bn]
makeAdderMod :: Int -> Integer -> [ STRef s Bool ] -> [ STRef s Bool ] -> ST s (OP s)
makeAdderMod n m as bs = 
  do ms <- mapM newSTRef (fromInt n m)
     t <- newSTRef False
     adder1 <- makeAdder n as bs
     adder2 <- makeAdder n ms bs
     return (adder1 :.: invert adder2) -- TO BE CTD
  
------------------------------------------------------------------------------
-- Testing

test :: Bool
test = runST $
  do ra <- newSTRef False
     rb <- newSTRef True
     rc <- newSTRef False
     interpM (sumOP ra rb rc)
     readSTRef rc

test2 :: Bool
test2 = runST $
  do ra <- newSTRef False
     rb <- newSTRef True
     rc <- newSTRef False
     interpM (invert (sumOP ra rb rc))
     readSTRef rc

test3 :: [Bool]
test3 = runST $
  do as <- mapM newSTRef [False, True, False]
     bs <- mapM newSTRef [False, False, True]
     adderOP <- makeAdder 3 as bs
     interpM adderOP
     mapM readSTRef bs

------------------------------------------------------------------------------
