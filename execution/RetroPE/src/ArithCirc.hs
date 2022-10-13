module ArithCirc where

import Prelude hiding (seq)

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))

import Control.Monad.ST (ST)

import ModularArith (doublemods, sqmods, invsqmods)
import Value (Value(zero), fromInt)
import Variable (Var, newVars, newVar)
import GToffoli (GToffoli(GToffoli), cx, ccx, ncx)
import Circuits (OP, Circuit(..), cop, ncop, ccop)

------------------------------------------------------------------------------
-- Circuits to perform arithmetic

-- Addition, multiplication, and modular exponentiation circuits

copyOP :: [br] -> [br] -> OP br
copyOP as bs = S.fromList (zipWith cx as bs)

carryOP :: br -> br -> br -> br -> OP br
carryOP c a b c' = S.fromList [ccx a b c', cx a b, ccx c b c']

sumOP :: br -> br -> br -> OP br
sumOP c a b = S.fromList [cx a b, cx c b]
  
makeAdder :: Value v => Int -> [ Var s v ] -> [ Var s v ] -> ST s (OP (Var s v))
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

makeAdderMod :: Value v => Int -> Integer -> [ Var s v ] -> [ Var s v ] -> ST s (OP (Var s v))
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
               Var s v -> [ Var s v ] -> [ Var s v ] -> ST s (OP (Var s v))
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
              [ Var s v ] -> [ Var s v ] -> [ Var s v ] -> ST s (OP (Var s v))
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
               
------------------------------------------------------------------------------


