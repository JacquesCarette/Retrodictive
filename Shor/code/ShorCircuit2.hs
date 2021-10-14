{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}

-- Following:
-- Quantum Networks for Elementary Arithmetic Operations
-- Vlatko Vedral, Adriano Barenco and Artur Ekert

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
import qualified GHC.List as GL
  
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
  | NCX (Var s) (Var s)
  | CCX (Var s) (Var s) (Var s)
  | COP (Var s) (OP s)
  | (:.:) (OP s) (OP s)
{--
    CCX :: OP (Bool,Bool,Bool) (Bool,Bool,Bool)
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
invert (NCX a b) = NCX a b
invert (CCX a b c) = CCX a b c
invert (COP a op) = COP a (invert op)
invert (op1 :.: op2) = invert op2 :.: invert op1
{--
invert CCX = CCX
invert (op1 :*: op2)    = invert op1 :*: invert op2
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
size (NCX _ _)         = 1
size (CCX _ _ _)       = 1
size (COP _ op)        = size op
size (op1 :.: op2)     = size op1 + size op2
{--
size (op1 :*: op2)    = size op1 + size op2
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
interpM (NCX a b) = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  writeSTRef b (sb, if va then vb else not vb)
interpM (CCX a b c) = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  (sc,vc) <- readSTRef c
  writeSTRef c (sc, if va && vb then not vc else vc)
interpM (COP a op) = do
  (sa,va) <- readSTRef a
  if va then interpM op else return ()
interpM (op1 :.: op2) =
  do interpM op1 ; interpM op2
{--
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
showM (NCX a b) d = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  return (printf "%sNCX (%s,%s) (%s,%s)" d sa (show va) sb (show vb))
showM (CCX a b c) d = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  (sc,vc) <- readSTRef c
  return (printf "%sCCX (%s,%s) (%s,%s) (%s,%s)" d sa (show va) sb (show vb) sc (show vc))
showM (COP a op) d = do
  (sa,va) <- readSTRef a
  s <- showM op ("  " ++ d)
  return (printf "%sCOP (%s,%s) (\n%s)" d sa (show va) s)
showM (op1 :.: op2) d = do
  s1 <- showM op1 d
  s2 <- showM op2 d
  return (printf "%s :.:\n%s" s1 s2)

------------------------------------------------------------------------------
-- Helpers for defining circuits

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

------------------------------------------------------------------------------
-- Actual circuits 

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b =
  CX a b :.: CX c b

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' =
  CCX a b c' :.:
  CX a b :.:
  CCX c b c'

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = foldr (:.:) ID (zipWith CX as bs)

--           n    [a0,a1,...an][b0,b1,...bn]
makeAdder :: Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder n as bs =
  do cs <- vars "c" (replicate (n+2) False)
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
  do ms <- vars "m" (fromInt (n+1) m)
     ms' <- vars "m'" (fromInt (n+1) m)
     t <- var "t" False
     adderab <- makeAdder n as bs
     addermb <- makeAdder n ms bs
     return $
       adderab :.:
       invert addermb :.:
       NCX (bs !! n) t :.: 
       COP t (copyOP ms' ms) :.:
       addermb :.: 
       copyOP ms' ms :.:
       invert adderab :.:
       CX (bs !! n) t :.:
       adderab

--
-- cMulMod :: 

------------------------------------------------------------------------------
-- Testing

adderGen :: Gen (Int,Integer,Integer)
adderGen =
  do n <- chooseInt (1, 100)
     a <- chooseInteger (0,2^n-1)
     b <- chooseInteger (0,2^n-1)
     return (n,a,b)

prop_add :: Property
prop_add = forAll adderGen $ \ (n, a, b) -> runST $ 
  do as <- vars "a" (fromInt (n+1) a)
     bs <- vars "b" (fromInt (n+1) b)
     adder <- makeAdder n as bs
     interpM adder
     bs <- mapM readSTRef bs
     let actual = toInt (map snd bs)
     return (actual === a+b)

adderModGen :: Gen (Int,Integer,Integer,Integer)
adderModGen =
  do n <- chooseInt (1, 100)
     m <- chooseInteger (1,2^n-1)
     a <- chooseInteger (0,m-1)
     b <- chooseInteger (0,m-1)
     return (n,m,a,b)

prop_addmod :: Property
prop_addmod = forAll adderModGen $ \ (n, m, a, b) -> runST $
  do as <- vars "a" (fromInt (n+1) a)
     bs <- vars "b" (fromInt (n+1) b)
     adderMod <- makeAdderMod n m as bs
     interpM adderMod
     bs <- mapM readSTRef bs
     let actual = toInt (map snd bs)
     return (actual === (a+b) `mod` m)

------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- Run all tests

return []                  -- ... weird TH hack !!!
checks = $quickCheckAll

------------------------------------------------------------------------------
------------------------------------------------------------------------------

