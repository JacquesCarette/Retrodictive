module Circuits where

-- Circuit defined over abstract values

import Prelude hiding (seq)

import Data.Maybe (catMaybes, maybe, fromMaybe, fromJust)
import Data.List (find,union,intercalate,delete,(\\),intersect,sort,nub)

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))

import Control.Lens hiding (op,(:<))
import Control.Monad 
import Control.Monad.ST
import Data.STRef

import System.Random (randomRIO)
import GHC.Integer.GMP.Internals (powModInteger)
  
import Text.Printf (printf)
import Test.QuickCheck hiding ((><))
import Control.Exception.Assert (assert, assertMessage)
import qualified Debug.Trace as Debug

import Numeric
import Value

----------------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

--
-- A circuit is a sequence of generalized Toffoli gates
-- ----------------------------------------------------

type OP s v = Seq (GToffoli s v)

data GToffoli s v = GToffoli [Bool] [Var s v] (Var s v)
  deriving Eq

showGToffoli :: Value v => GToffoli s v -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %s %s (%s)\n"
    (show (map fromEnum bs))
    (show controls)
    (show vt)

showOP :: Value v => OP s v -> ST s String
showOP = foldMap showGToffoli

sizeOP :: OP s v -> [(Int,Int)]
sizeOP = foldr (\(GToffoli cs _ _) -> incR (length cs)) [] 
  where incR n [] = [(n,1)]
        incR n ((g,r):gs) | n == g = (g,r+1) : gs
                          | otherwise = (g,r) : incR n gs

showSizes :: [(Int,Int)] -> String
showSizes [] = ""
showSizes ((g,r) : gs) =
  printf "Generalized Toffoli Gates with %d controls = %d\n" g r
  ++ showSizes gs

--
-- Addition, multiplication, and modular exponentiation circuits
-- -------------------------------------------------------------

xop :: Var s v -> GToffoli s v
xop = GToffoli [] []

cx :: Var s v -> Var s v -> GToffoli s v
cx a = GToffoli [True] [a]

ncx :: Var s v -> Var s v -> GToffoli s v
ncx a = GToffoli [False] [a]

ccx :: Var s v -> Var s v -> Var s v -> GToffoli s v
ccx a b = GToffoli [True,True] [a,b]

cop :: Var s v -> OP s v -> OP s v
cop c = fmap (\ (GToffoli bs cs t) -> GToffoli (True:bs) (c:cs) t)
  
ncop :: Var s v -> OP s v -> OP s v
ncop c = fmap (\ (GToffoli bs cs t) -> GToffoli (False:bs) (c:cs) t)

ccop :: OP s v -> [Var s v] -> OP s v
ccop = foldr cop

carryOP :: Var s v -> Var s v -> Var s v -> Var s v -> OP s v
carryOP c a b c' = S.fromList [ccx a b c', cx a b, ccx c b c']

sumOP :: Var s v -> Var s v -> Var s v -> OP s v
sumOP c a b = S.fromList [cx a b, cx c b]
  
copyOP :: [Var s v] -> [Var s v] -> OP s v
copyOP as bs = S.fromList (zipWith cx as bs)

makeAdder :: Value v => Int -> [ Var s v ] -> [ Var s v ] -> ST s (OP s v)
makeAdder n as bs = do
  cs <- newVars (fromInt n 0)
  return (loop as bs cs)
    where loop [a,_] [b,b'] [c] =
            carryOP c a b b' ><
            singleton (cx a b) ><
            sumOP c a b
          loop (a:as) (b:bs) (c:c':cs) =
            carryOP c a b c' ><
            loop as bs (c':cs) ><
            S.reverse (carryOP c a b c') ><
            sumOP c a b

makeAdderMod :: Value v => Int -> Integer -> [ Var s v ] -> [ Var s v ] -> ST s (OP s v)
makeAdderMod n m as bs = do
  ms <- newVars (fromInt (n+1) m)
  ms' <- newVars (fromInt (n+1) m)
  t <- newVar zero
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

makeCMulMod :: Value v => Int -> Integer -> Integer ->
               Var s v -> [ Var s v ] -> [ Var s v ] -> ST s (OP s v)
makeCMulMod n a m c xs ts = do
  ps <- newVars (fromInt (n+1) 0)
  as <- mapM
          (newVars . fromInt (n+1))
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

makeExpMod :: Value v => Int -> Integer -> Integer ->
              [ Var s v ] -> [ Var s v ] -> [ Var s v ] -> ST s (OP s v)
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
-- Circuit abstraction

{--

                -------------
       xs -----|             |----- xs
               |     op      | 
 ancillasIns --|             |----- ancillaOuts
                -------------
 
  ancillaVals 
f    - to initialize ancillaIns in forward evaluation, or
    - to compare with result of retrodictive execution
 
  forward eval: set ancillaIns to ancillaVals; set xs to input; run; check ancillaOuts

  retrodictive: set xs to symbolic; set ancillaOuts to input; run; check ancillaInss against ancillaVals

--}

data Circuit s v = Circuit
  { op          :: OP s v
  , xs          :: [Var s v]
  , ancillaIns  :: [Var s v]
  , ancillaOuts :: [Var s v]  
  , ancillaVals :: [v]
  }

-- 

-- a^x mod m

expm :: Value v => Int -> Integer -> Integer -> ST s (Circuit s v)
expm n a m = do
  xs <- newVars (fromInt (n+1) 0)
  ts <- newVars (fromInt (n+1) 0)
  us <- newVars (fromInt (n+1) 0)
  op <- makeExpMod n a m xs ts us
  return $ Circuit
    { op           = op
    , xs           = xs
    , ancillaIns   = ts
    , ancillaOuts  = if odd n then ts else us
    , ancillaVals  = fromInt (n+1) 1
    }
               
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

