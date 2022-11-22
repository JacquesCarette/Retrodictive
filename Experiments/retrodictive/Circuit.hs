{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}

module Circuit where

import Control.Monad 
import Control.Monad.ST
import Control.Exception.Assert (assert, assertMessage)

import Data.STRef
import qualified Data.Sequence as S
import Data.Sequence (Seq,singleton,(><))
import Data.Maybe (catMaybes)

import Text.Printf (printf)

--

import Numeric
import ANF

----------------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

--
-- Locations where values are stored
-- ---------------------------------<

type Var s = STRef s Value

-- Stateful functions to deal with variables

newVar :: Bool -> ST s (Var s)
newVar = newSTRef . newValue

newVars :: [Bool] -> ST s [Var s]
newVars = mapM newVar

newDynVar :: STRef s Int -> String -> ST s (Var s)
newDynVar gensym s = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newDynValue (s ++ show k))

newDynVars :: STRef s Int -> String -> Int -> ST s [Var s]
newDynVars gensym s n = replicateM n (newDynVar gensym s)

newDynS :: String -> ST s (Var s)
newDynS = newSTRef . newDynValue 

updateVarB :: Var s -> Bool -> ST s ()
updateVarB x b = writeSTRef x (fromBool b)

updateVarsB :: [Var s] -> [Bool] -> ST s ()
updateVarsB xs bs = mapM_ (uncurry updateVarB) (zip xs bs)

--
-- A circuit is a sequence of generalized Toffoli gates
-- ----------------------------------------------------

type OP s = Seq (GToffoli s)

data GToffoli s = GToffoli [Bool] [Var s] (Var s)
  deriving Eq

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli [] [] t) = do
  vt <- readSTRef t
  return $ printf "x %s;" (show vt)
showGToffoli (GToffoli [b] [c] t) = do
  control <- readSTRef c
  vt <- readSTRef t
  if b
    then return $ printf "cx %s %s;" (show control) (show vt)
    else return $ printf "x %s; cx %s %s; x %s;"
    (show control) (show control) (show vt) (show control) 
showGToffoli (GToffoli [b1,b2] [c1,c2] t) = do
  [control1,control2] <- mapM readSTRef [c1,c2]
  vt <- readSTRef t
  if | b1 && b2 ->
       return $ printf "ccx %s %s %s;"
       (show control1) (show control2) (show vt)
     | b1 && not b2 ->
       return $ printf "x %s; ccx %s %s %s; x %s;"
       (show control2) (show control1) (show control2) (show vt) (show control2)
     | not b1 && not b2 ->
       return $ printf "x %s; ccx %s %s %s; x %s;"
       (show control1) (show control1) (show control2) (show vt) (show control1)
     | otherwise -> 
       return $ printf "x %s; x %s; ccx %s %s %s; x %s; x %s;"
       (show control1) (show control2)
       (show control1) (show control2) (show vt)
       (show control1) (show control2)
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %s %s (%s)"
    (show (map fromEnum bs))
    (show controls)
    (show vt)

showOP :: OP s -> ST s String
showOP = foldMap showGToffoli

--
-- Addition, multiplication, and modular exponentiation circuits
-- -------------------------------------------------------------

xop :: Var s -> GToffoli s
xop b = GToffoli [] [] b

cx :: Var s -> Var s -> GToffoli s
cx a b = GToffoli [True] [a] b

ncx :: Var s -> Var s -> GToffoli s
ncx a b = GToffoli [False] [a] b

ccx :: Var s -> Var s -> Var s -> GToffoli s
ccx a b c = GToffoli [True,True] [a,b] c

nnccx :: Var s -> Var s -> Var s -> GToffoli s
nnccx a b c = GToffoli [False,False] [a,b] c

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
makeAdder n as bs = do
  cs <- newVars (fromInt n 0)
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
makeAdderMod n m as bs = do
  ms <- newVars (fromInt (n+1) m)
  ms' <- newVars (fromInt (n+1) m)
  t <- newVar False
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

makeCMulMod :: Int -> Integer -> Integer ->
               Var s -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeCMulMod n a m c xs ts = do
  ps <- newVars (fromInt (n+1) 0)
  as <- mapM
          (\a -> newVars (fromInt (n+1) a))
          (take (n+1) (doublemods a m))
  adderPT <- makeAdderMod n m ps ts
  return (loop adderPT as xs ps)
    where loop adderPT [] [] ps =
            ncop c (copyOP xs ts) 
          loop adderPT (a:as) (x:xs) ps =
            ccop (copyOP a ps) [c,x] ><
            adderPT ><
            ccop (copyOP a ps) [c,x] ><
            loop adderPT as xs ps

-- if n odd, result is in ts
-- if n even, result is in us

makeExpMod :: Int -> Integer -> Integer ->
              [ Var s ] -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeExpMod n a m xs ts us = do
  let sqs = take (n+1) (sqmods a m)
  let invsqs = take (n+1) (invsqmods a m)
  makeStages 0 n sqs invsqs m xs ts us
    where
      makeStages i n [] [] m [] ts us = return S.empty
      makeStages i n (sq:sqs) (invsq:invsqs) m (c:cs) ts us
        | even i = do
            mulsqMod <- makeCMulMod n sq m c ts us
            mulinvsqMod <- makeCMulMod n invsq m c us ts
            rest <- makeStages (i+1) n sqs invsqs m cs ts us
            return (mulsqMod ><
                    S.reverse mulinvsqMod ><
                    rest)
        | otherwise = do
            mulsqMod <- makeCMulMod n sq m c us ts
            mulinvsqMod <- makeCMulMod n invsq m c ts us
            rest <- makeStages (i+1) n sqs invsqs m cs ts us
            return (mulsqMod ><
                    S.reverse mulinvsqMod ><
                    rest)

----------------------------------------------------------------------------------------
-- Circuit Abstraction

data Circuit s = Circuit
  { op   :: OP s 
  , ins  :: [Var s]
  , outs :: [Var s]
  }

data Dir = Forward | Backward deriving Eq

----------------------------------------------------------------------------------------
-- Evaluation

evalGToffoli :: [Bool] -> [Value] -> Var s -> Value -> ST s ()
evalGToffoli bs xs tx tv = 
  let cfs = foldr (\ (b,x) r -> sand r (if b then x else snot x)) true (zip bs xs)
  in writeSTRef tx (sxor cfs tv)

evalOp :: OP s -> ST s ()
evalOp = mapM_ (\ g@(GToffoli bs cs t) -> do
                   controls <- mapM readSTRef cs
                   tv <- readSTRef t
                   evalGToffoli bs controls t tv)

evalCircuit :: Circuit s -> Dir -> ST s [Value]
evalCircuit (Circuit {op,ins,outs}) dir = do
  let (op',vars,vars') = if dir == Forward
                         then (op,ins,outs)
                         else (S.reverse op,outs,ins)
  evalOp op'
  mapM readSTRef vars'

----------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------
