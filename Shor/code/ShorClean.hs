-- Following:
-- Quantum Networks for Elementary Arithmetic Operations
-- Vlatko Vedral, Adriano Barenco and Artur Ekert

module ShorClean where

import GHC.Integer.GMP.Internals

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, (><))

import Control.Monad.ST
import Data.STRef
  
------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits

type Var s = STRef s Bool

data GToffoli s = GToffoli [Bool] [Var s] (Var s)

type OP s = Seq (GToffoli s)

interpGT :: GToffoli s -> ST s ()
interpGT (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  if and (zipWith (==) bs controls)
    then writeSTRef t (not vt)
    else return ()

interpM :: OP s -> ST s ()
interpM = foldMap interpGT
   
-- Shorthands

cx :: Var s -> Var s -> GToffoli s
cx a b = GToffoli [True] [a] b

ncx :: Var s -> Var s -> GToffoli s
ncx a b = GToffoli [False] [a] b

ccx :: Var s -> Var s -> Var s -> GToffoli s
ccx a b c = GToffoli [True,True] [a,b] c

cop :: Var s -> OP s -> OP s
cop c = fmap (\ (GToffoli bs cs t) -> GToffoli (True:bs) (c:cs) t)

ncop :: Var s -> OP s -> OP s
ncop c = fmap (\ (GToffoli bs cs t) -> GToffoli (False:bs) (c:cs) t)

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

------------------------------------------------------------------------------
-- Plain addder (Fig. 2 in paper)
-- adds two n-bit numbers (modulo 2^(n+1))
-- in reverse, subtracts (modulo 2^(n+1))

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' = S.fromList [ccx a b c', cx a b, ccx c b c']

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b = S.fromList [cx a b, cx c b]

-- as = [a0,a1,...an-1, 0]
-- bs = [b0,b1,...bn-1, 0]]

makeAdder :: Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder n as bs =
  do cs <- mapM newSTRef (fromInt n 0)
     return (loop as bs cs)
       where loop [a,_] [b,b'] [c] =
               (carryOP c a b b') ><
               (singleton (cx a b)) ><
               (sumOP c a b)
             loop (a:as) (b:bs) (c:c':cs) =
               (carryOP c a b c') ><
               (loop as bs (c':cs)) ><
               (S.reverse (carryOP c a b c')) ><
               (sumOP c a b)

------------------------------------------------------------------------------
-- Adder modulo m (Fig. 4 in paper)

-- adds two (n+1)-bit numbers (modulo m)
-- in reverse, subtracts (modulo m)

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = S.fromList (zipWith cx as bs)

-- as = [a0,a1,...an-1,an]
-- bs = [b0,b1,...bn-1,bn]
-- ms = [m0,m1,...mn-1, 0] (most significant bit = 0)
-- a < m and b < m

makeAdderMod :: Int -> Integer -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdderMod n m as bs = 
  do ms <- mapM newSTRef (fromInt (n+1) m)
     ms' <- mapM newSTRef (fromInt (n+1) m)
     t <- newSTRef False
     adderab <- makeAdder n as bs
     addermb <- makeAdder n ms bs
     return $
       adderab ><
       S.reverse addermb ><
       singleton (ncx (bs !! n) t) ><
       cop t (copyOP ms' ms) ><
       addermb ><
       cop t (copyOP ms' ms) ><
       S.reverse adderab ><
       singleton (cx (bs !! n) t) ><
       adderab

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
  do ps <- mapM newSTRef (fromInt (n+1) 0)
     as <- mapM (\a -> mapM newSTRef (fromInt (n+1) a)) (take (n+1) (doublemods a m))
     adderPT <- makeAdderMod n m ps ts
     return (loop adderPT as xs ps)
       where loop adderPT [] [] ps =
               ncop c (copyOP xs ts) 
             loop adderPT (a:as) (x:xs) ps =
               ccop (copyOP a ps) [c,x] ><
               adderPT ><
               ccop (copyOP a ps) [c,x] ><
               loop adderPT as xs ps

-------------------------------------------------------------------------------
-- Modular exponentiation (Fig. 6 in paper)

-- Compute (a ^ x) `mod` m

-- precompute a, a^2, a^4, ... `mod` m
-- and a, a^(-2), a^(-4), ... `mod` m

sqmods :: Integer -> Integer -> [Integer]
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
makeStages i n [] [] m [] ts us = return S.empty
makeStages i n (sq:sqs) (invsq:invsqs) m (c:cs) ts us
  | even i =
      do mulsqMod <- makeCMulMod n sq m c ts us
         mulinvsqMod <- makeCMulMod n invsq m c us ts
         rest <- makeStages (i+1) n sqs invsqs m cs ts us
         return (mulsqMod ><
                 S.reverse mulinvsqMod ><
                 rest)
  | otherwise = 
      do mulsqMod <- makeCMulMod n sq m c us ts
         mulinvsqMod <- makeCMulMod n invsq m c ts us
         rest <- makeStages (i+1) n sqs invsqs m cs ts us
         return (mulsqMod ><
                 S.reverse mulinvsqMod ><
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

------------------------------------------------------------------------------
-- > map shor15 [0..10]
-- [1,7,4,13,1,7,4,13,1,7,4]
-- <
-- Pick 13 and evaluate backwards symbolically

shor15 :: Integer -> Integer
shor15 x = runST $
  do xs <- mapM newSTRef (fromInt (n+1) x)
     ts <- mapM newSTRef (fromInt (n+1) 1)
     us <- mapM newSTRef (fromInt (n+1) 0)
     circuit <- makeExpMod n 7 15 xs ts us
     interpM circuit
     res <- mapM readSTRef us 
     return (toInt res)
       where n = 4


------------------------------------------------------------------------------

