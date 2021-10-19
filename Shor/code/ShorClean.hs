-- Following:
-- Quantum Networks for Elementary Arithmetic Operations
-- Vlatko Vedral, Adriano Barenco and Artur Ekert

module ShorClean where

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, (><))

import Control.Monad.ST
import Data.STRef
  
------------------------------------------------------------------------------
-- Integer helpers

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

toInt :: [Bool] -> Integer
toInt bs = foldr (\ b n -> toInteger (fromEnum b) + 2*n) 0 bs

-- precompute a, 2a, 4a, 8a, ... `mod` m

doublemods :: Integer -> Integer -> [Integer]
doublemods a m = a : doublemods ((2*a) `mod` m) m

-- precompute a, a^2, a^4, ... `mod` m
-- and a, a^(-2), a^(-4), ... `mod` m

sqmods :: Integer -> Integer -> [Integer]
sqmods a m = am : sqmods (am * am) m
  where am = a `mod` m

-- https://stackoverflow.com/questions/13096491/
-- multiplicative-inverse-of-modulo-m-in-scheme

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
   
------------------------------------------------------------------------------
-- Building blocks

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

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' = S.fromList [ccx a b c', cx a b, ccx c b c']

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b = S.fromList [cx a b, cx c b]

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = S.fromList (zipWith cx as bs)

------------------------------------------------------------------------------
-- Plain addder (Fig. 2 in paper)
-- adds two n-bit numbers (modulo 2^(n+1))
-- in reverse, subtracts (modulo 2^(n+1))

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
       where
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

------------------------------------------------------------------------------
-- Examples

-- Shor parameters: base and toFactor must be coprime

data ShorParams =
  ShorParams { numberOfBits :: Int
             , base         :: Integer
             , toFactor     :: Integer
             }

p15a = ShorParams {
  numberOfBits = 4, 
  base         = 7, 
  toFactor     = 15
  }

p15b = ShorParams {
  numberOfBits = 5, 
  base         = 7, 
  toFactor     = 15
  }

p21 = ShorParams {
  numberOfBits = 6, 
  base         = 5, 
  toFactor     = 21
  }

p323 = ShorParams {
  numberOfBits = 10, 
  base         = 49, 
  toFactor     = 323
  }

shor :: ShorParams -> Integer -> Integer
shor (ShorParams { numberOfBits = n, base = a, toFactor = m}) x = runST $ 
  do xs <- mapM newSTRef (fromInt (n+1) x)
     ts <- mapM newSTRef (fromInt (n+1) 1)
     us <- mapM newSTRef (fromInt (n+1) 0)
     circuit <- makeExpMod n a m xs ts us
     interpM circuit
     res <- if even n then mapM readSTRef us else mapM readSTRef ts
     return (toInt res)

{--

Below pass parameters directly:

*ShorClean> map (shor 4 7 15) [0..10]
[
 1,7,4,13,
 1,7,4,13,
 1,7,4
]

*ShorClean> map (shor 5 7 15) [0..10]
[
 1,7,4,13,
 1,7,4,13,
 1,7,4
]

*ShorClean> map (shor 6 5 21) [0..20]
[
 1,5,4,20,16,17,
 1,5,4,20,16,17,
 1,5,4,20,16,17,
 1,5,4
]

*ShorClean> map (shor 10 49 323) [0..60]
[
 1,49,140,77,220,121,115,144,273,134,106,26,305,87,64,229,239,83,191,315,254,172,30,178,
 1,49,140,77,220,121,115,144,273,134,106,26,305,87,64,229,239,83,191,315,254,172,30,178,
 1,49,140,77,220,121,115,144,273,134,106,26,305
]

--}

-- if (shor p) x = r
-- then (invShor p) x r = (x,1,0) 


invShor :: ShorParams -> Integer -> Integer -> (Integer,Integer,Integer)
invShor (ShorParams { numberOfBits = n, base = a, toFactor = m}) x res = runST $ 
  do xs <- mapM newSTRef (fromInt (n+1) x)
     ts <- if odd n
           then mapM newSTRef (fromInt (n+1) res)
           else mapM newSTRef (fromInt (n+1) 0)
     us <- if even n
           then mapM newSTRef (fromInt (n+1) res)
           else mapM newSTRef (fromInt (n+1) 0)
     circuit <- makeExpMod n a m xs ts us
     interpM (S.reverse circuit)
     ixs <- mapM readSTRef xs
     its <- mapM readSTRef ts
     ius <- mapM readSTRef us
     return (toInt ixs, toInt its, toInt ius)

-- How circuit size grows with number of bits

shorSize :: Int -> Int
shorSize n = runST $
  do xs <- mapM newSTRef (fromInt (n+1) 0)
     ts <- mapM newSTRef (fromInt (n+1) 0)
     us <- mapM newSTRef (fromInt (n+1) 0)
     circuit <- makeExpMod n 2 3 xs ts us
     return (S.length circuit)

{--

[
 (1,328),      (2,1530),     (3,4128),     (4,8650),      (5,15624),
 (6,25578),    (7,39040),    (8,56538),    (9,78600),    (10,105754),
(11,138528),  (12,177450),  (13,223048),  (14,275850),   (15,336384),
(16,405178),  (17,482760),  (18,569658),  (19,666400),   (20,773514),
(21,891528),  (22,1020970), (23,1162368), (24,1316250),  (25,1483144),
(26,1663578), (27,1858080), (28,2067178), (29,2291400),  (30,2531274),
(31,2787328), (32,3060090), (33,3350088), (34,3657850),  (35,3983904),
(36,4328778), (37,4693000), (38,5077098), (39,5481600),  (40,5907034),
(41,6353928), (42,6822810), (43,7314208), (44,7828650),  (45,8366664),
(46,8928778), (47,9515520), (48,10127418),(49,10765000), (50,11428794),
(51,12119328),(52,12837130),(53,13582728),(54,14356650), (55,15159424),
(56,15991578),(57,16853640),(58,17746138),(59,18669600), (60,19624554),
(61,20611528),(62,21631050),(63,22683648),(64,23769850), (65,24890184),
(66,26045178),(67,27235360),(68,28461258),(69,29723400), (70,31022314),
(71,32358528),(72,33732570),(73,35144968),(74,36596250), (75,38086944),
(76,39617578),(77,41188680),(78,42800778),(79,44454400), (80,46150074),
(81,47888328),(82,49669690),(83,51494688),(84,53363850), (85,55277704),
(86,57236778),(87,59241600),(88,61292698),(89,63390600), (90,65535834),
(91,67728928),(92,69970410),(93,72260808),(94,74600650), (95,76990464),
(96,79430778),(97,81922120),(98,84465018),(99,87060000),(100,89707594)
]

--}

------------------------------------------------------------------------------

