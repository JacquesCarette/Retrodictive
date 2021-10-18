{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiWayIf #-}

-- Following:
-- Quantum Networks for Elementary Arithmetic Operations
-- Vlatko Vedral, Adriano Barenco and Artur Ekert

module ShorWIP where

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

data Bit = Bool Bool | Dynamic String | DynamicNot String
  deriving (Eq,Show)

negBit :: Bit -> Bit 
negBit (Bool b) = Bool (not b)
negBit (Dynamic s) = DynamicNot s
negBit (DynamicNot s) = Dynamic s

controlsInactive :: [Bool] -> [Bit] -> Bool
controlsInactive bs controls = or (zipWith check bs controls)
  where check b (Bool b') = b /= b'
        check b _ = False

--

type Var s = STRef s (String,Bit)

data OP s = 
    ID
  | (:.:) (OP s) (OP s)
  | GTOFFOLI [Bool] [Var s] (Var s)
  -- debugging
  | PRINT String [Var s] String
  | ASSERT [Var s] Integer

showOP :: OP s -> ST s String
--showOP ID = return "ID"
showOP (ID :.: op) = showOP op
showOP (op :.: ID) = showOP op
showOP (op1 :.: op2) =
  do s1 <- showOP op1
     s2 <- showOP op2
     return (printf "%s\n%s" s1 s2)
showOP (GTOFFOLI bs cs t) = do
  controls <- mapM readSTRef cs
  target <- readSTRef t
  return (printf "GTOFFOLI %s %s %s"
          (show bs)
          (show controls)
          (show target))
showOP _ = return ""

size :: OP s -> Int
size ID                 = 1
size (op1 :.: op2)      = size op1 + size op2
size (GTOFFOLI bs cs t) = 1
-- 
size (PRINT _ _ _) = 0
size (ASSERT _ _) = 0

invert :: OP s -> OP s
invert ID                 = ID
invert (op1 :.: op2)      = invert op2 :.: invert op1
invert (GTOFFOLI bs cs t) = GTOFFOLI bs cs t
--
invert (PRINT sb xs sa) = PRINT sa xs sb
invert (ASSERT xs i) = ASSERT xs i

interpM :: OP s -> ST s ()
interpM ID                 = return () 
interpM (op1 :.: op2)      = do interpM op1 ; interpM op2
interpM (GTOFFOLI bs cs t) = do
  controls <- mapM readSTRef cs
  target <- readSTRef t
  if and (zipWith (\ b (_, Bool c) -> b == c) bs controls)
    then writeSTRef t (fst target, negBit (snd target))
    else return ()
interpM (PRINT sb xs sa) = do
  svs <- mapM readSTRef xs
  let names = concat (map fst svs)
  let value = toInt (map (\ (_, Bool b) -> b) svs)
  trace (printf "%s%s = %d%s" sb names value sa) (return ())
interpM (ASSERT xs i) = do
  svs <- mapM readSTRef xs
  let names = concat (map fst svs)
  let value = toInt (map (\ (_, Bool b) -> b) svs)
  assertMessage "" (printf "Expecting %s = %d but found %d" names i value)
    (assert (value == i)) (return ())

   
-- Shorthands

cx :: Var s -> Var s -> OP s
cx a b = GTOFFOLI [True] [a] b

ncx :: Var s -> Var s -> OP s
ncx a b = GTOFFOLI [False] [a] b

ccx :: Var s -> Var s -> Var s -> OP s
ccx a b c = GTOFFOLI [True,True] [a,b] c

cop :: Var s -> OP s -> OP s
cop c ID                 = ID
cop c (op1 :.: op2)      = cop c op1 :.: cop c op2
cop c (GTOFFOLI bs cs t) = GTOFFOLI (True:bs) (c:cs) t

ncop :: Var s -> OP s -> OP s
ncop c ID                 = ID
ncop c (op1 :.: op2)      = ncop c op1 :.: ncop c op2
ncop c (GTOFFOLI bs cs t) = GTOFFOLI (False:bs) (c:cs) t

ccop :: OP s -> [Var s] -> OP s
ccop = foldr cop 

------------------------------------------------------------------------------
-- Helpers for defining and testing circuits

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

toInt :: [Bool] -> Integer
toInt bs = foldr (\ b n -> toInteger (fromEnum b) + 2*n) 0 bs

var :: String -> Bool -> ST s (Var s)
var s v = newSTRef (s,Bool v)

vars :: String -> [Bool] -> ST s [Var s]
vars s vs = mapM (\ (v,i) -> newSTRef (s ++ show i, Bool v))
                 (zip vs [0..(length vs)])

dvars :: String -> Int -> ST s [Var s]
dvars s n = mapM (\ i -> newSTRef (s ++ show i, Dynamic (s ++ show i)))
                 [0..(n-1)]

------------------------------------------------------------------------------
-- Plain addder (Fig. 2 in paper)
-- adds two n-bit numbers (modulo 2^(n+1))
-- in reverse, subtracts (modulo 2^(n+1))

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' = ccx a b c' :.: cx a b :.: ccx c b c'

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b = cx a b :.: cx c b

-- as = [a0,a1,...an-1, 0]
-- bs = [b0,b1,...bn-1, 0]]

makeAdder :: Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder n as bs =
  do cs <- vars "c" (fromInt n 0)
     return (loop as bs cs)
       where loop [a,_] [b,b'] [c] =
               carryOP c a b b' :.:
               cx a b :.:
               sumOP c a b 
             loop (a:as) (b:bs) (c:c':cs) =
               carryOP c a b c' :.:
               loop as bs (c':cs) :.:
               invert (carryOP c a b c') :.:
               sumOP c a b 

-- Tests

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
     let actual = toInt (map (\ (_, Bool b) -> b) bs)
     return (actual === (a+b) `mod` (2 ^ (n+1)))

prop_sub :: Property
prop_sub = forAll adderGen $ \ (n, a, b) -> runST $ 
  do as <- vars "a" (fromInt (n+1) a)
     bs <- vars "b" (fromInt (n+1) b)
     adder <- makeAdder n as bs
     interpM (invert adder)
     bs <- mapM readSTRef bs
     let actual = toInt (map (\ (_, Bool b) -> b) bs)
     return (actual === (b-a) `mod` (2 ^ (n+1)))

------------------------------------------------------------------------------
-- Adder modulo m (Fig. 4 in paper)

-- adds two (n+1)-bit numbers (modulo m)
-- in reverse, subtracts (modulo m)

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = foldr (:.:) ID (zipWith cx as bs)

-- as = [a0,a1,...an-1,an]
-- bs = [b0,b1,...bn-1,bn]
-- ms = [m0,m1,...mn-1, 0] (most significant bit = 0)
-- a < m and b < m

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
       cop t (copyOP ms' ms) :.:
       invert adderab :.:
       cx (bs !! n) t :.:
       adderab

-- Tests

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
     let actual = toInt (map (\ (_, Bool b) -> b) bs)
     return (actual === (a+b) `mod` m)

prop_submod :: Property
prop_submod = forAll adderModGen $ \ (n, m, a, b) -> runST $
  do as <- vars "a" (fromInt (n+1) a)
     bs <- vars "b" (fromInt (n+1) b)
     adderMod <- makeAdderMod n m as bs
     interpM (invert adderMod)
     bs <- mapM readSTRef bs
     let actual = toInt (map (\ (_, Bool b) -> b) bs)
     return (actual === (b-a) `mod` m)

------------------------------------------------------------------------------
-- Controlled multiplier modulo m (Fig. 5 in paper)

-- if control is true
--   multiply an (n+1)-bit number 'x' by a fixed (n+1)-bit number 'a'
-- else
--   return 'x'

-- precompute a, 2a, 4a, 8a, ... `mod` m

doublemods :: Integer -> Integer -> [Integer]
doublemods a m = a : doublemods ((2*a) `mod` m) m

-- as = [a0,a1,...an-1, 0] (most significant bit = 0)
-- ms = [m0,m1,...mn-1, 0] (most significant bit = 0)
-- c  = the control bit
-- xs = [x0,x1,...xn-1,xn] 
-- ts = [ 0, 0, .... 0, 0]
-- a < m

makeCMulMod :: Int -> Integer -> Integer -> Var s -> [ Var s ] -> [ Var s ]
            -> ST s (OP s)
makeCMulMod n a m c xs ts =
  do ps <- vars "p" (fromInt (n+1) 0)
     as <- mapM (\a -> vars "a" (fromInt (n+1) a)) (take (n+1) (doublemods a m))
     adderPT <- makeAdderMod n m ps ts
     return (loop adderPT as xs ps)
       where loop adderPT [] [] ps =
               ncop c (copyOP xs ts) 
             loop adderPT (a:as) (x:xs) ps =
               ccop (copyOP a ps) [c,x] :.:
               adderPT :.:
               ccop (copyOP a ps) [c,x] :.:
               loop adderPT as xs ps

-- Tests

cMulModGen :: Gen (Int,Integer,Bool,Integer,Integer)
cMulModGen =
  do n <- chooseInt (1, 100) 
     m <- chooseInteger (1,2^n-1)
     c <- elements [False,True]
     x <- chooseInteger (0,2^(n+1)-1)
     a <- chooseInteger (0,m-1)
     return (n,m,c,x,a)

prop_cmulmod :: Property
prop_cmulmod = forAll cMulModGen $ \ (n, m, c, x, a) -> runST $
  do cvar <- var "c" c
     xs <- vars "x" (fromInt (n+1) x)
     ts <- vars "t" (fromInt (n+1) 0)
     cMulMod <- makeCMulMod n a m cvar xs ts
     interpM cMulMod
     ts <- mapM readSTRef ts
     let actual = toInt (map (\ (_, Bool b) -> b) ts)
     return (actual === if c then (a * x) `mod` m else x)

prop_cdivmod :: Property
prop_cdivmod = forAll cMulModGen $ \ (n, m, c, x, a) -> runST $
  do cvar <- var "c" c
     xs <- vars "x" (fromInt (n+1) x)
     ts <- if c
           then vars "t" (fromInt (n+1) ((a * x) `mod` m))
           else vars "t" (fromInt (n+1) x)
     cMulMod <- makeCMulMod n a m cvar xs ts
     interpM (invert cMulMod)
     ts <- mapM readSTRef ts
     let actual = toInt (map (\ (_, Bool b) -> b) ts)
     return (actual === 0)

-------------------------------------------------------------------------------
-- Modular exponentiation (Fig. 6 in paper)

-- Compute (a ^ x) `mod` m

-- precompute a, a^2, a^4, ... `mod` m
-- and a, a^(-2), a^(-4), ... `mod` m

sqmods :: Integer -> Integer -> [Integer]
-- sqmods a m = a : sqmods ((a * a) `mod` m) m
sqmods a m = am : sqmods (am * am) m
  where am = a `mod` m

-- https://stackoverflow.com/questions/13096491/multiplicative-inverse-of-modulo-m-in-scheme
invmod :: Integer -> Integer -> Integer
invmod x m = loop x m 0 1
  where
    loop 0 1 a _ = a `mod` m
    loop 0 _ _ _ = error "Inputs not coprime"
    loop x b a u = loop (b `mod` x) x u (a - (u * (b `div` x)))

invsqmods :: Integer -> Integer -> [Integer]
invsqmods a m = invam : invsqmods (am * am) m
  where am = a `mod` m
        invam = a `invmod` m 

makeStages :: Int -> Int -> [Integer] -> [Integer] -> Integer
          -> [Var s] -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeStages i n [] [] m [] ts us = return ID
makeStages i n (sq:sqs) (invsq:invsqs) m (c:cs) ts us
  | even i =
      do mulsqMod <- makeCMulMod n sq m c ts us
         mulinvsqMod <- makeCMulMod n invsq m c us ts
         rest <- makeStages (i+1) n sqs invsqs m cs ts us
         return (mulsqMod :.:
                 invert mulinvsqMod :.:
                 rest)
  | otherwise = 
      do mulsqMod <- makeCMulMod n sq m c us ts
         mulinvsqMod <- makeCMulMod n invsq m c ts us
         rest <- makeStages (i+1) n sqs invsqs m cs ts us
         return (mulsqMod :.:
                 invert mulinvsqMod :.:
                 rest)

-- as = [a0,a1,...an-1, 0] (most significant bit = 0)
-- ms = [m0,m1,...mn-1, 0] (most significant bit = 0)
-- xs = [x0,x1,...xn-1,xn] 
-- ts = [ 1, 0, .... 0, 0]
-- us = [ 0, 0, .... 0, 0]
-- a < m
-- for all i, gcd(a^(2i),m) = 1

makeExpMod :: Int -> Integer -> Integer -> [ Var s ] -> [ Var s ] -> [ Var s ]
            -> ST s (OP s)
makeExpMod n a m xs ts us = 
  do let sqs = take (n+1) (sqmods a m)
     let invsqs = take (n+1) (invsqmods a m)
     makeStages 0 n sqs invsqs m xs ts us

-- Tests

expModGen :: Gen (Int,Integer,Integer,Integer)
expModGen = 
  do n <- chooseInt (2, 50) 
     m <- chooseInteger (2,2^n-1)
     x <- chooseInteger (0,2^(n+1)-1)
     a <- suchThat (chooseInteger (1,m-1)) (\a -> gcd a m == 1) 
     return (n,m,x,a)

prop_expmod :: Property
prop_expmod = forAll expModGen $ \ (n, m, x, a) -> runST $
  do xs <- vars "x" (fromInt (n+1) x)
     ts <- vars "t" (fromInt (n+1) 1)
     us <- vars "u" (fromInt (n+1) 0)
     expMod <- makeExpMod n a m xs ts us
     interpM expMod
     res <- if odd n then mapM readSTRef ts else mapM readSTRef us
     let actual = toInt (map (\ (_, Bool b) -> b) res)
     return (actual === powModInteger a x m)

-------------------------------------------------------------------------------
-- Run all tests

return []                  -- ... weird TH hack !!!
test = $quickCheckAll

------------------------------------------------------------------------------
-- Factoring 15
-- 
-- n = 7
-- a = 7
-- m = 15
-- x ranges 0..255 (which is greater than 15 * 15)
-- t initially 1
-- u initially 0

shor15 :: Integer -> Integer
shor15 x = runST $
  do xs <- vars "x" (fromInt (n+1) x)
     ts <- vars "t" (fromInt (n+1) 1)
     us <- vars "u" (fromInt (n+1) 0)
     circuit <- makeExpMod n 7 15 xs ts us
     interpM circuit
     res <- mapM readSTRef us 
     return (toInt (map (\ (_, Bool b) -> b) res))
       where n = 4
     
-- > map shor15 [0..10]
-- [1,7,4,13,1,7,4,13,1,7,4]
-- <
-- Pick 13 and evaluate backwards symbolically

shor15Prog :: IO () 
shor15Prog = writeFile "shor15Prog.txt" $ runST $
  do xs <- dvars "x" (n+1)
     ts <- vars "t" (fromInt (n+1) 0)
     us <- vars "u" (fromInt (n+1) 13)
     circuit <- makeExpMod n 7 15 xs ts us
     showOP (invert circuit)
       where n = 4

shor15PE :: Int
shor15PE = runST $
  do xs <- dvars "x" (n+1)
     ts <- vars "t" (fromInt (n+1) 0)
     us <- vars "u" (fromInt (n+1) 13)
     circuit <- makeExpMod n 7 15 xs ts us
     trace (printf "Circuit has %d GTOFFOLI gates" (size circuit)) $ return ()
     interpM (invert circuit)
     res1 <- mapM readSTRef xs
     res2 <- mapM readSTRef ts
     res3 <- mapM readSTRef us
     trace (printf "\n*** TERMINATED ***\n") $ 
       trace (printf "xs = %s\n" (show res1)) $ 
       trace (printf "ts = %s\n" (show res2)) $ 
       trace (printf "us = %s\n" (show res3)) $
       return 0
       where n = 4

go = shor15PE

------------------------------------------------------------------------------
