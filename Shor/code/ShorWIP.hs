{-# LANGUAGE MultiWayIf #-}

module ShorWIP where

import Data.List (intersect) 

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, (><))

import Control.Monad.ST
import Data.STRef
  
import Text.Printf
import Test.QuickCheck hiding ((><))
import Control.Exception.Assert
import qualified Debug.Trace as Debug

----------------------------------------------------------------------------------------
-- Simple helpers

debug = True

trace :: String -> a -> a
trace s a = if debug then Debug.trace s a else a

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

toInt :: [Bool] -> Integer
toInt bs = foldr (\ b n -> toInteger (fromEnum b) + 2*n) 0 bs

doublemods :: Integer -> Integer -> [Integer]
doublemods a m = a : doublemods ((2*a) `mod` m) m

sqmods :: Integer -> Integer -> [Integer]
sqmods a m = am : sqmods (am * am) m
  where am = a `mod` m

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

----------------------------------------------------------------------------------------
-- Circuits are sequences of generalized Toffoli gates

type Var s = STRef s Bool

data GToffoli s = GToffoli [Bool] [Var s] (Var s)

type OP s = Seq (GToffoli s)

--

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

----------------------------------------------------------------------------------------
-- Standard evaluation

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
-- Example circuits

data Params =
  Params { numberOfBits :: Int
         , base         :: Integer
         , toFactor     :: Integer
         }

p15a = Params {
  numberOfBits = 4, 
  base         = 7, 
  toFactor     = 15
  }

p15b = Params {
  numberOfBits = 5, 
  base         = 7, 
  toFactor     = 15
  }

p21 = Params {
  numberOfBits = 6, 
  base         = 5, 
  toFactor     = 21
  }

p323 = Params {
  numberOfBits = 10, 
  base         = 49, 
  toFactor     = 323
  }

shorCircuit :: Params -> Integer -> ST s (OP s)
shorCircuit (Params {numberOfBits = n, base = a, toFactor = m}) x = 
  do xs <- mapM newSTRef (fromInt (n+1) x)
     ts <- mapM newSTRef (fromInt (n+1) 1)
     us <- mapM newSTRef (fromInt (n+1) 0)
     makeExpMod n a m xs ts us

------------------------------------------------------------------------------
-- Partial evaluation

-- Merge phase
-- Attempt to merge gates with the same target

merge :: GToffoli s -> GToffoli s -> Either (GToffoli s) (GToffoli s, GToffoli s)
merge g1@(GToffoli bs1 cs1 t1) g2@(GToffoli bs2 cs2 t2)
  | t1 /= t2 = Right (g1,g2)
  | otherwise = error "todo"

mergePhase :: OP s -> ST s (OP s)
mergePhase op = do

  trace
    (printf "Merge Phase:\n************\nInput circuit has %d gates\n" (S.length op))
    (return ())

  opr <- return op

  trace (printf "Resulting circuit has %d gates\n" (S.length opr)) $
    return opr

testMerge :: () 
testMerge = runST $ 
  do op <- shorCircuit p15a 0
     mergePhase op
     return () 

------------------------------------------------------------------------------

{--



Current idea:

groupBy targe:
  swapping gates with different targets (even no write to control)

merge gates with same target
  either cancel each other, or
  produce bigger list of controls


repeat

---

g1
g2

==>

g2
g1

canSwap g1 g2 :
  target(g1) /= target(g2) &&
  target(g1) not in controls(g2) 
  target(g2) not in controls(g1) 




--}



{--

data Bit = Bool Bool | Dynamic String | DynamicNot String
  | AND Bit Bit --- Mmmm
  deriving (Eq,Show)

isStatic :: Bit -> Bool
isStatic (Bool _) = True
isStatic _ = False

isDynamic :: Bit -> Bool
isDynamic (Dynamic _) = True
isDynamic _ = False

isDynamicNot :: Bit -> Bool
isDynamicNot (DynamicNot _) = True
isDynamicNot _ = False

isStaticB :: Bool -> Bit -> Bool
isStaticB b (Bool b') = b == b'
isStaticB _ _ = False

negBit :: Bit -> Bit 
negBit (Bool b) = Bool (not b)
negBit (Dynamic s) = DynamicNot s
negBit (DynamicNot s) = Dynamic s

controlsInactive :: [Bool] -> [Bit] -> Bool
controlsInactive bs controls = or (zipWith check bs controls)
  where check b (Bool b') = b /= b'
        check b _ = False

controlsStatic :: [Bit] -> Bool
controlsStatic controls = all isStatic controls

removeRedundant :: [Bool] -> [ Var s ] -> ST s ([Bool],[Var s])
removeRedundant [] [] = return ([],[])
removeRedundant (b:bs) (x:xs) =
  do (s,v) <- readSTRef x
     if | isStaticB b v ->
          removeRedundant bs xs
        | otherwise ->
          do (bs',xs') <- removeRedundant bs xs
             return (b:bs', x:xs')

interpM :: OP s -> ST s ()
interpM ID                 = return () 
interpM (op1 :.: op2)      = do interpM op1 ; interpM op2
interpM (GTOFFOLI bs' cs' t) = do
  controls' <- mapM readSTRef cs'
  target <- readSTRef t
  (bs,cs) <- removeRedundant bs' cs'
  controls <- mapM readSTRef cs
  if | controlsStatic (map snd controls) -> 
       if and (zipWith (\ b (_, Bool c) -> b == c) bs controls)
       then writeSTRef t (fst target, negBit (snd target))
       else return ()
  
  ---------- SPECIAL CASES ---------

     | length bs < length bs' ->
       interpM (GTOFFOLI bs cs t)

     | controlsInactive bs (map snd controls) ->
       return ()

       -- CX d 0 => d d
     | length bs == 1 &&
       and bs && 
       isDynamic (snd (head controls)) &&
       isStaticB False (snd target) ->
       writeSTRef t (fst target, snd (head controls))

       -- NCX d 0 => d dn
     | length bs == 1 &&
       all not bs && 
       isDynamic (snd (head controls)) &&
       isStaticB False (snd target) ->
       writeSTRef t (fst target, negBit (snd (head controls)))

       -- CX dn 0 => dn dn
     | length bs == 1 && 
       and bs && 
       isDynamicNot (snd (head controls)) &&
       isStaticB False (snd target) ->
       writeSTRef t (fst target, snd (head controls))

       -- CX d d => d 0
     | length bs == 1 && 
       and bs && 
       isDynamic (snd (head controls)) &&
       isDynamic (snd target) &&
       snd (head controls) == snd target -> 
       writeSTRef t (fst target, Bool False)

       -- NCX d d => d 1
     | length bs == 1 && 
       all not bs && 
       isDynamic (snd (head controls)) &&
       isDynamic (snd target) &&
       snd (head controls) == snd target -> 
       writeSTRef t (fst target, Bool True)

       -- NCX d 1 => d d
     | length bs == 1 && 
       all not bs && 
       isDynamic (snd (head controls)) &&
       isStaticB True (snd target) ->
       writeSTRef t (fst target, snd (head controls))

       -- CX dn dn => dn 0
     | length bs == 1 && 
       and bs && 
       isDynamicNot (snd (head controls)) &&
       isDynamicNot (snd target) &&
       snd (head controls) == snd target -> 
       writeSTRef t (fst target, Bool False)

       -- CX d dn => d 1
     | length bs == 1 && 
       and bs && 
       isDynamic (snd (head controls)) &&
       isDynamicNot (snd target) &&
       snd (head controls) == negBit (snd target) -> 
       writeSTRef t (fst target, Bool True)

       -- CX d 1 => d dn
     | length bs == 1 && 
       and bs && 
       isDynamic (snd (head controls)) &&
       isStaticB True (snd target)  -> 
       writeSTRef t (fst target, negBit (snd (head controls)))

       -- CX dn d => dn 1
     | length bs == 1 && 
       and bs && 
       isDynamicNot (snd (head controls)) &&
       isDynamic (snd target) &&
       snd (head controls) == negBit (snd target) -> 
       writeSTRef t (fst target, Bool True)

       -- CX dn 1 => dn d
     | length bs == 1 && 
       and bs && 
       isDynamicNot (snd (head controls)) &&
       isStaticB True (snd target) ->
       writeSTRef t (fst target, negBit (snd (head controls)))

       -- CCX d d 0 => d d d
     | length bs == 2 &&
       and bs && 
       isDynamic (snd (controls !! 0)) && 
       isDynamic (snd (controls !! 1)) &&
       isStaticB False (snd target) &&
       snd (controls !! 0) == snd (controls !! 1) ->
       writeSTRef t (fst target, snd (controls !! 0))

       -- CCX d d d => d d 0
     | length bs == 2 &&
       and bs && 
       isDynamic (snd (controls !! 0)) && 
       isDynamic (snd (controls !! 1)) &&
       isDynamic (snd target) &&
       snd (controls !! 0) == snd (controls !! 1) &&
       snd (controls !! 0) == snd target ->
       writeSTRef t (fst target, Bool False)

       -- CCX dn dn d => dn dn 1
     | length bs == 2 &&
       and bs && 
       isDynamicNot (snd (controls !! 0)) && 
       isDynamicNot (snd (controls !! 1)) &&
       isDynamic (snd target) &&
       snd (controls !! 0) == snd (controls !! 1) &&
       snd (controls !! 0) == negBit (snd target) ->
       writeSTRef t (fst target, Bool True)

       -- CCX dn dn 1 => dn dn d
     | length bs == 2 &&
       and bs && 
       isDynamicNot (snd (controls !! 0)) && 
       isDynamicNot (snd (controls !! 1)) &&
       isStaticB True (snd target) &&
       snd (controls !! 0) == snd (controls !! 1) -> 
       writeSTRef t (fst target, negBit (snd (controls !! 0)))

       -- CCX dn dn 0 => dn dn dn
     | length bs == 2 &&
       and bs && 
       isDynamicNot (snd (controls !! 0)) && 
       isDynamicNot (snd (controls !! 1)) &&
       isStaticB False (snd target) &&
       snd (controls !! 0) == snd (controls !! 1) -> 
       writeSTRef t (fst target, snd (controls !! 0))

       -- CCX dn dn dn => dn dn 0
     | length bs == 2 &&
       and bs && 
       isDynamicNot (snd (controls !! 0)) && 
       isDynamicNot (snd (controls !! 1)) &&
       isDynamicNot (snd target) && 
       snd (controls !! 0) == snd (controls !! 1) &&
       snd (controls !! 0) == snd target -> 
       writeSTRef t (fst target, Bool False)

     | length bs == 2 &&
       (not (bs !! 0) && bs !! 1) &&
       isDynamic (snd (controls !! 0)) && 
       isDynamicNot (snd (controls !! 1)) &&
       isStaticB True (snd target) && 
       snd (controls !! 0) == negBit (snd (controls !! 1)) ->
       writeSTRef t (fst target, snd (controls !! 0))

     | length bs == 2 &&
       (not (bs !! 0) && bs !! 1) &&
       isDynamic (snd (controls !! 0)) && 
       isDynamic (snd (controls !! 1)) &&
       snd (controls !! 0) == snd (controls !! 1) ->
       return () 

     | length bs == 2 &&
       and bs && 
       isDynamic (snd (controls !! 0)) && 
       isDynamicNot (snd (controls !! 1)) &&
       snd (controls !! 0) == negBit (snd (controls !! 1)) ->
       return () 

  ----------------------------------
       
     | otherwise ->
         error (printf "%s\n\nGTOFFOLI %s %s %s\n\n%s"
                (replicate 20 '*')
                (show bs)
                (show controls)
                (show target)
                (replicate 35 '*'))
       
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

--}
