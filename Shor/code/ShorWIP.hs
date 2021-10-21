{-# LANGUAGE MultiWayIf #-}

module ShorWIP where

import Data.Maybe
import Data.List

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, (><))

import Control.Monad 
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

--
-- Values with either static or dynamic information

data Value = Value { name  :: String
                   , value :: Maybe Bool
                   }

instance Show Value where
  show (Value {name = s, value = Nothing}) = s ++ " _"
  show (Value {name = s, value = Just True}) = s ++ " 1"
  show (Value {name = s, value = Just False}) = s ++ " 0"

newValue :: String -> Bool -> Value
newValue s b = Value { name = s, value = Just b }

newDynValue :: String -> Value
newDynValue s = Value { name = s, value = Nothing }

isStatic :: Value -> Bool
isStatic (Value {value = Nothing}) = False
isStatic _ = True

extractBool :: Value -> Bool
extractBool (Value { value = Just b }) = b
extractBool _ = error "Expecting a static variable"

negValue :: Value -> Value 
negValue v = v { value = Just (not (extractBool v)) }
                   
valueToInt :: [Value] -> Integer
valueToInt v = toInt $ map extractBool v

-- returns yes/no/unknown as Just True, Just False, Nothing

controlsActive :: [Bool] -> [Value] -> Maybe Bool
controlsActive bs cs =
  if | not r' -> Just False
     | Nothing `elem` r -> Nothing
     | otherwise -> Just True
  where r' = and (catMaybes r)
        r = zipWith f bs cs
        f b (Value { value = Just b' }) = Just (b == b')
        f b _ = Nothing

--
-- Locations where values are stored

type Var s = STRef s Value

newVar :: STRef s Int -> String -> Bool -> ST s (Var s)
newVar gensym s b = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newValue (s ++ (show k)) b)

newVars :: STRef s Int -> String -> [Bool] -> ST s [Var s]
newVars gensym s = mapM (newVar gensym s)

newDynVar :: STRef s Int -> String -> ST s (Var s)
newDynVar gensym s = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newDynValue (s ++ (show k)))

newDynVars :: STRef s Int -> String -> Int -> ST s [Var s]
newDynVars gensym s n = replicateM n (newDynVar gensym s)

--
-- Gates and circuits

data GToffoli s = GToffoli [Bool] [Var s] (Var s)

type OP s = Seq (GToffoli s)

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %s %s (%s)\n" (show bs) (show controls) (show vt)

showOP :: OP s -> ST s String
showOP = foldMap showGToffoli

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

makeAdder :: STRef s Int -> Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder gensym n as bs = do
  cs <- newVars gensym "carryAdder" (fromInt n 0)
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

makeAdderMod :: STRef s Int -> Int -> Integer -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdderMod gensym n m as bs = do
  ms <- newVars gensym "modAdder" (fromInt (n+1) m)
  ms' <- newVars gensym "modAdder'" (fromInt (n+1) m)
  t <- newVar gensym "tempAdder" False
  adderab <- makeAdder gensym n as bs
  addermb <- makeAdder gensym n ms bs
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

makeCMulMod :: STRef s Int -> Int -> Integer -> Integer ->
               Var s -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeCMulMod gensym n a m c xs ts = do
  ps <- newVars gensym "pMul" (fromInt (n+1) 0)
  as <- mapM
          (\a -> newVars gensym "aMul" (fromInt (n+1) a))
          (take (n+1) (doublemods a m))
  adderPT <- makeAdderMod gensym n m ps ts
  return (loop adderPT as xs ps)
    where loop adderPT [] [] ps =
            ncop c (copyOP xs ts) 
          loop adderPT (a:as) (x:xs) ps =
            ccop (copyOP a ps) [c,x] ><
            adderPT ><
            ccop (copyOP a ps) [c,x] ><
            loop adderPT as xs ps

makeExpMod :: STRef s Int -> Int -> Integer -> Integer ->
              [ Var s ] -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeExpMod gensym n a m xs ts us = do
  let sqs = take (n+1) (sqmods a m)
  let invsqs = take (n+1) (invsqmods a m)
  makeStages 0 n sqs invsqs m xs ts us
    where
      makeStages i n [] [] m [] ts us = return S.empty
      makeStages i n (sq:sqs) (invsq:invsqs) m (c:cs) ts us
        | even i = do
            mulsqMod <- makeCMulMod gensym n sq m c ts us
            mulinvsqMod <- makeCMulMod gensym n invsq m c us ts
            rest <- makeStages (i+1) n sqs invsqs m cs ts us
            return (mulsqMod ><
                    S.reverse mulinvsqMod ><
                    rest)
        | otherwise = do
            mulsqMod <- makeCMulMod gensym n sq m c us ts
            mulinvsqMod <- makeCMulMod gensym n invsq m c ts us
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
  let ca = controlsActive bs controls
  if ca == Just True 
    then writeSTRef t (negValue vt)
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
shorCircuit (Params {numberOfBits = n, base = a, toFactor = m}) x = do
  gensym <- newSTRef 0
  xs <- newVars gensym "x" (fromInt (n+1) x)
  ts <- newVars gensym "t" (fromInt (n+1) 1)
  us <- newVars gensym "u" (fromInt (n+1) 0)
  makeExpMod gensym n a m xs ts us

runShor :: Params -> Integer -> Integer
runShor p@(Params { numberOfBits = n, base = a, toFactor = m}) x = runST $ do
  gensym <- newSTRef 0
  xs <- newVars gensym "x" (fromInt (n+1) x)
  ts <- newVars gensym "t" (fromInt (n+1) 1)
  us <- newVars gensym "u" (fromInt (n+1) 0)
  circuit <- makeExpMod gensym n a m xs ts us
  interpM circuit
  res <- if even n then mapM readSTRef us else mapM readSTRef ts
  return (valueToInt res)

invShor :: Params -> Integer -> String
invShor (Params { numberOfBits = n, base = a, toFactor = m}) res = runST $ do
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" (n+1)
  ts <- if odd n
        then newVars gensym "t" (fromInt (n+1) res)
        else newVars gensym "t" (fromInt (n+1) 0)
  us <- if even n
        then newVars gensym "u" (fromInt (n+1) res)
        else newVars gensym "u" (fromInt (n+1) 0)
  circuit <- makeExpMod gensym n a m xs ts us

  -- Phase I of PE
  simplified <- simplifyPhase circuit

  showOP simplified

{--

  printState "Initially:" xs ts us

--  resetVars n res ts us

  -- Phase II of PE

  -- add gensym'ed names
  -- GROUP BY SAME TARGET; MERGE; AND SIMPLIFY
  -- ADD SPECIAL CASES CX(X,0) = (X,X) ETC (needs aliasing)

--  resetVars n res ts us

  printState "Final state:" xs ts us
  {--
  let rcircuit = simplified
  interpM (S.reverse rcircuit)
  ixs <- mapM readSTRef xs
  its <- mapM readSTRef ts
  ius <- mapM readSTRef us
  return (valueToInt ixs, valueToInt its, valueToInt ius)
  --}
    where
{--
      resetVars n res ts us =
        let resbits = map newValue $ fromInt (n+1) res
        in if odd n
           then do mapM_ (uncurry writeSTRef) (zip ts resbits)
                   mapM_ (\t -> writeSTRef t (newValue False)) us
           else do mapM_ (uncurry writeSTRef) (zip us resbits)
                   mapM_ (\t -> writeSTRef t (newValue False)) ts
--}
      printState msg xs ts us = do
        ixs <- mapM readSTRef xs
        its <- mapM readSTRef ts
        ius <- mapM readSTRef us
        trace
          (printf "%s\nxs = %s;\nts = %s;\nus = %s\n"
            msg (show ixs) (show its) (show ius))
          (return ())
--}

go :: IO ()
go = writeFile "tmp.txt" (invShor p15a 1)

------------------------------------------------------------------------------
-- Partial evaluation

-- Remove redundant controls
-- If all static controls, execute the instruction

simplify :: GToffoli s -> ST s (OP s)
simplify g@(GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  let ca = controlsActive bs controls
  if | ca == Just True && isStatic vt -> do
         writeSTRef t (negValue vt)
         return S.empty
     | ca == Just False ->
         return S.empty
     | otherwise -> do -- mark target as unknown
         writeSTRef t (Value { name = name vt, value = Nothing })
         return (S.singleton g)

simplifyPhase :: OP s -> ST s (OP s)
simplifyPhase op = do

  trace
    (printf "***************\nSimplify Phase:\n***************") $
    trace (printf "Input circuit has %d gates" (S.length op)) $
    return ()

  opr <- foldM (\ op' g -> do g' <- simplify g; return (op' >< g')) S.empty op

  trace (printf "Resulting circuit has %d gates\n" (S.length opr)) $
    return opr

testSimplify :: () 
testSimplify = runST $ do
  op <- shorCircuit p15a 0
  simplifyPhase op
  return () 

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
testMerge = runST $ do
  op <- shorCircuit p15a 0
  mergePhase op
  return () 

------------------------------------------------------------------------------
------------------------------------------------------------------------------


