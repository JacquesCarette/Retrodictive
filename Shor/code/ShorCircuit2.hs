{-# LANGUAGE TemplateHaskell #-}

-- Following:
-- Quantum Networks for Elementary Arithmetic Operations
-- Vlatko Vedral, Adriano Barenco and Artur Ekert

module Shor where

import GHC.Integer.GMP.Internals
import Control.Monad.ST
import Data.STRef
  
import Text.Printf
import Test.QuickCheck
import Control.Exception.Assert
import qualified Debug.Trace as Debug

-- Toggle 

--debug = False
debug = True

trace :: String -> a -> a
trace s a = if debug then Debug.trace s a else a

------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Syntax

type Var s = STRef s (String,Bool)

data OP s = 
    ID
  | GTOFFOLI [Bool] [Var s] (Var s)
  | (:.:) (OP s) (OP s)

invert :: OP s -> OP s
invert ID                 = ID
invert (GTOFFOLI bs cs t) = GTOFFOLI bs cs t
invert (op1 :.: op2)      = invert op2 :.: invert op1
       
size :: OP s -> Int
size ID                 = 1
size (GTOFFOLI bs cs t) = 1
size (op1 :.: op2)      = size op1 + size op2

--

cx :: Var s -> Var s -> OP s
cx a b = GTOFFOLI [True] [a] b

ncx :: Var s -> Var s -> OP s
ncx a b = GTOFFOLI [False] [a] b

ccx :: Var s -> Var s -> Var s -> OP s
ccx a b c = GTOFFOLI [True,True] [a,b] c

cop :: Var s -> OP s -> OP s
cop c ID = ID
cop c (GTOFFOLI bs cs t) = GTOFFOLI (True:bs) (c:cs) t
cop c (op1 :.: op2) = cop c op1 :.: cop c op2

------------------------------------------------------------------------------
-- Monadic interpreter

interpM :: OP s -> ST s ()
interpM ID = return () 
interpM (GTOFFOLI bs cs t) = do
  controls <- mapM readSTRef cs
  (st,vt) <- readSTRef t
  if and (zipWith (\ b (_,c) -> b == c) bs controls)
    then writeSTRef t (st, not vt)
    else return ()
interpM (op1 :.: op2) =
  do interpM op1 ; interpM op2
 
------------------------------------------------------------------------------
-- Helpers for defining circuits

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

toInt :: [Bool] -> Integer
toInt bs = foldr (\ b n -> toInteger (fromEnum b) + 2*n) 0 bs

var :: String -> Bool -> ST s (Var s)
var s v = newSTRef (s,v)

vars :: String -> [Bool] -> ST s [Var s]
vars s vs = mapM (\ (v,i) -> newSTRef (s ++ show i, v))
                 (zip vs [0..(length vs)])

------------------------------------------------------------------------------
-- Actual circuits 

-- Fig. 2 in paper

--           n    [a0,a1,...an][b0,b1,...bn]
makeAdder :: Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder n as bs =
  do cs <- vars "c" (fromInt (n+2) 0)
     return (loop as bs cs)
       where loop [a] [b] [c,c'] =
               carryOP c a b c' :.:
               cx a b :.:
               sumOP c a b
             loop (a:as) (b:bs) (c:c':cs) =
               carryOP c a b c' :.:
               loop as bs (c':cs) :.:
               invert (carryOP c a b c') :.:
               sumOP c a b

-- Fig. 3i in paper

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' = ccx a b c' :.: cx a b :.: ccx c b c'

-- Fig. 3ii in paper

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b = cx a b :.: cx c b

-- Needed for Fig. 4

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = foldr (:.:) ID (zipWith cx as bs)

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
       ncx (bs !! n) t :.: 
       cop t (copyOP ms' ms) :.:
       addermb :.: 
       copyOP ms' ms :.:
       invert adderab :.:
       cx (bs !! n) t :.:
       adderab

{--

-- Needed for Fig. 5

shiftOP :: [ Var s ] -> OP s
shiftOP xs = loop (reverse xs)
  where loop [x1,x0] = SWAP x1 x0
        loop (x:y:xs) = SWAP x y :.: loop (y:xs)

-- Fig. 5 in paper

--             n      a          m          c      [x0,x1,...xn] [t0,t1,..,tn]
makeCMulMod :: Int -> Integer -> Integer -> Var s -> [ Var s ] -> [ Var s ]
            -> ST s (OP s)
makeCMulMod n a m c xs ts =
  do ps <- vars "p" (fromInt (n+1) 0)
     as <- vars "a" (fromInt (n+1) a)
     adderPT <- makeAdderMod n m ps ts
     return (loop adderPT as c xs ps ts)
       where loop adderPT as c [] ps ts = 
               NCOP c (copyOP xs ts)
             loop adderPT as c (x:xs) ps ts = 
               CCOP c x (copyOP as ps) :.:
               adderPT :.:
               CCOP c x (copyOP as ps) :.:
               shiftOP as :.:
               loop adderPT as c xs ps ts

-- Fig. 6 in paper

--expMod 

--}

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

prop_sub :: Property
prop_sub = forAll adderGen $ \ (n, a, b) -> runST $ 
  do as <- vars "a" (fromInt (n+1) a)
     bs <- vars "b" (fromInt (n+1) b)
     adder <- makeAdder n as bs
     interpM (invert adder)
     bs <- mapM readSTRef bs
     let actual = toInt (map snd bs)
     return (actual === (b-a) `mod` (2 ^ (n+1))) 

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

prop_submod :: Property
prop_submod = forAll adderModGen $ \ (n, m, a, b) -> runST $
  do as <- vars "a" (fromInt (n+1) a)
     bs <- vars "b" (fromInt (n+1) b)
     adderMod <- makeAdderMod n m as bs
     interpM (invert adderMod)
     bs <- mapM readSTRef bs
     let actual = toInt (map snd bs)
     return (actual === (b-a) `mod` m)

-- For multiplication, we want the most significant half of bits in
-- 'a' to be 0

{--
cMulModGen :: Gen (Int,Integer,Bool,Integer,Integer)
cMulModGen =
  do n <- return 4 -- chooseInt (1, 10) -- 100
     m <- return 15 -- chooseInteger (1,2^n-1)
     c <- return False -- elements [False,True]
     x <- chooseInteger (0,2^n-1)
     a <- return 2 -- chooseInteger (0,2^(n `div` 2)-1)
     return (n,m,c,x,a)

xprop_cmulmod :: Property
xprop_cmulmod = forAll cMulModGen $ \ (n, m, c, x, a) -> runST $
  do cvar <- var "c" c
     xs <- vars "x" (fromInt (n+1) x)
     ts <- vars "t" (fromInt (n+1) 0)
     cMulMod <- makeCMulMod n a m cvar xs ts
     interpM cMulMod
     ts <- mapM readSTRef ts
     let actual = toInt (map snd ts)
     return (actual === if c then (a * x) `mod` m else x)
--}

-------------------------------------------------------------------------------
-- Run all tests

return []                  -- ... weird TH hack !!!
test = $quickCheckAll

------------------------------------------------------------------------------
------------------------------------------------------------------------------

