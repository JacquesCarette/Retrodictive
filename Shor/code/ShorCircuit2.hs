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

--debug = False
debug = True

trace :: String -> a -> a
trace s a = if debug then Debug.Trace.trace s a else a

------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Syntax

data Bit = Static Bool | Dynamic String deriving Show
type Var s = STRef s (String,Bit)

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
  case (va,vb) of
    (Static ba, Static bb) -> 
      writeSTRef b (sb, Static $ if ba then not bb else bb)
    (x,y) -> error (printf "CX %s %s not done" (show x) (show y))
interpM (NCX a b) = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  case (va,vb) of
    (Static ba, Static bb) -> 
      writeSTRef b (sb, Static $ if ba then bb else not bb)
    (x,y) -> error (printf "NCX %s %s not done" (show x) (show y))
interpM (CCX a b c) = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  (sc,vc) <- readSTRef c
  case (va,vb,vc) of
    (Static ba, Static bb, Static bc) -> 
      writeSTRef c (sc, Static $ if ba && bb then not bc else bc)
    (x,y,z) -> error (printf "CCX %s %s %s not done" (show x) (show y) (show z))
interpM (COP a op) = do
  (sa,va) <- readSTRef a
  case va of
    Static ba -> 
      if ba then interpM op else return ()
    x -> error (printf "COP %s not done" (show x))
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
  return (printf "%sCX %s %s" d sa sb)
showM (NCX a b) d = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  return (printf "%sNCX %s %s" d sa sb)
showM (CCX a b c) d = do
  (sa,va) <- readSTRef a
  (sb,vb) <- readSTRef b
  (sc,vc) <- readSTRef c
  return (printf "%sCCX %s %s %s" d sa sb sc)
showM (COP a op) d = do
  (sa,va) <- readSTRef a
  s <- showM op ("  " ++ d)
  return (printf "%sCOP %s (\n%s)" d sa s)
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

toInt :: [Bit] -> Integer
toInt bs = foldr (\ (Static b) n -> toInteger (fromEnum b) + 2*n) 0 bs

var :: String -> Bool -> ST s (Var s)
var s v = newSTRef (s,Static v)

vars :: String -> [Bool] -> ST s [Var s]
vars s vs = mapM (\ (v,i) -> newSTRef (s ++ show i, Static v))
                 (zip vs [0..(length vs)])


dvars :: String -> [String] -> ST s [Var s]
dvars s vs = mapM (\ (v,i) -> newSTRef (s ++ show i, Dynamic v))
                 (zip vs [0..(length vs)])

------------------------------------------------------------------------------
-- Actual circuits 

-- Fig. 2 in paper

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

-- Fig. 3i in paper

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' =
  CCX a b c' :.:
  CX a b :.:
  CCX c b c'

-- Fig. 3ii in paper

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b =
  CX a b :.: CX c b

-- Needed for Fig. 4

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = foldr (:.:) ID (zipWith CX as bs)

-- Fig. 4 in paper

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

-- Fig. 5 in paper

--cMulMod 

-- Fig. 6 in paper

--expMod 

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

-- test minus

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

-- test minus mod M

-------------------------------------------------------------------------------
-- Run all tests

return []                  -- ... weird TH hack !!!
checks = $quickCheckAll

------------------------------------------------------------------------------
------------------------------------------------------------------------------

