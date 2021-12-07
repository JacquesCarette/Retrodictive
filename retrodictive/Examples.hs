module Examples where

import Control.Monad.ST
import Data.STRef
import qualified Data.Sequence as S
import Data.Sequence ((><))
import System.Random (randomRIO)
import GHC.Integer.GMP.Internals (powModInteger)
import Text.Printf (printf)

--

import Numeric
import ANF
import Circuit

---------------------------------------------------------------------------------------
-- Deutsch

deutsch :: Int -> ST s (Circuit s)
deutsch a = do 
  x <- newDynS "x"
  y <- newDynS "y"
  let op = [uzero,uone,uid,unot] !! a
  return $ Circuit { op = op x y, ins = [x], outs = [y] }
  where uzero x y = S.empty
        uone x y  = S.singleton $ xop y
        uid x y   = S.singleton $ cx x y
        unot x y  = S.singleton $ ncx x y

runDeutsch :: Int -> Bool -> Bool -> (Integer,Integer)
runDeutsch a b1 b2 = runST $ do
  c <- deutsch a
  updateVarB (head (ins c)) b1
  updateVarB (head (outs c)) b2
  evalCircuit c Forward
  x <- mapM readSTRef (ins c)
  y <- mapM readSTRef (outs c)
  return (valuesToInt x, valuesToInt y)

symbolicRunDeutsch :: Int -> Bool -> [Formula]
symbolicRunDeutsch a b = runST $ do
  c <- deutsch a 
  updateVarB (head (outs c)) b
  evalCircuit c Forward

retrodictiveRunDeutsch :: Int -> Bool -> String
retrodictiveRunDeutsch a b = runST $ do
  c <- deutsch a
  updateVarB (head (outs c)) b
  evalCircuit c Backward
  [v] <- mapM readSTRef (outs c)
  return $ show v

-- Deutsch-Jozsa
-- n = 2 (all cases)

deutschJozsa2 :: Int -> ST s (Circuit s)
deutschJozsa2 a = do
  let op = [djzero, djone, d1, d2, d3, d4, d5, d6 ] !! a
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" 2
  y <- newDynS "y"
  return $ Circuit { op = op xs y, ins = xs, outs = [y] }
  where djzero xs y = S.empty
        djone xs y = S.singleton (xop y)
        d1 [x0,x1] y = S.singleton (cx x1 y)
        d2 [x0,x1] y = S.singleton (ncx x1 y)
        d3 [x0,x1] y = S.singleton (cx x0 y)
        d4 [x0,x1] y = S.singleton (ncx x0 y)
        d5 [x0,x1] y = S.singleton (ccx x0 x1 y)
        d6 [x0,x1] y = S.singleton (nnccx x0 x1 y)

retrodictiveRunDeutschJozsa2 :: Int -> Bool -> String
retrodictiveRunDeutschJozsa2 a b = runST $ do
  c <- deutschJozsa2 a
  updateVarB (head (outs c)) b
  evalCircuit c Backward
  [v] <- mapM readSTRef (outs c)
  return $ show v

-- general n (one case)

deutschJozsaN :: Int -> Int -> ST s (Circuit s)
deutschJozsaN a n = do
  let op = [djzero, djone, djbalanced] !! a
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" n
  y <- newDynS "y"
  return $ Circuit { op = op xs y, ins = xs, outs = [y] }
  where djzero xs y = S.empty
        djone xs y = S.singleton (xop y)
        djbalanced xs y = foldMap (\x -> S.singleton (cx x y)) xs

retrodictiveRunDeutschJozsaN :: Int -> Int -> Bool -> String
retrodictiveRunDeutschJozsaN a n b = runST $ do
  c <- deutschJozsaN a n
  updateVarB (head (outs c)) b
  evalCircuit c Backward
  [v] <- mapM readSTRef (outs c)
  return $ show v

-- Bernstein-Vazirani

-- Given f(x0 x1 ... xn) = x0s0 + x1s1 + ... + xnsn for some s 
-- Find s

bernsteinVazirani :: Int -> Integer -> ST s (Circuit s)
bernsteinVazirani n u = do
  gensym <- newSTRef 0
  qvars <- newDynVars gensym "q" n
  target <- newVar False
  let us = fromInt n u
  return $ Circuit { op = c us qvars target, ins = qvars, outs = [target] }
  where c [] [] target = S.empty
        c (False : us) (uvar : uvars) target = c us uvars target
        c (True : us) (uvar : uvars) target =
          S.singleton (cx uvar target) >< c us uvars target

runBernsteinVazirani :: Int -> Integer -> Integer -> [Formula]
runBernsteinVazirani n u q = runST $ do
  c <- bernsteinVazirani n u
  updateVarsB (ins c) (fromInt n q)
  evalCircuit c Forward
  mapM readSTRef (outs c)

retrodictiveRunBernsteinVazirani :: Int -> Integer -> Bool -> [Formula]
retrodictiveRunBernsteinVazirani n u b = runST $ do
  c <- bernsteinVazirani n u
  updateVarB (head (outs c)) b
  evalCircuit c Backward
  rs <- mapM readSTRef (outs c)
  return rs

-- Simon




-- Optimized factor 21 from IBM experiment

simple21 :: Integer -> ST s (Circuit s)
simple21 c = do
  [c0,c1,c2] <- newVars (fromInt 3 c)
  q0 <- newVar False
  q1 <- newVar False
  let op = S.fromList
        [ cx c2 q1
        , cx c1 q1
        , cx q1 q0
        , ccx c1 q0 q1
        , cx q1 q0
        , xop q1
        , ccx c0 q1 q0
        , xop q1
        , cx q1 q0
        , ccx c0 q0 q1
        , cx q1 q0        
        ]
  return $ Circuit
    { op   = op
    , ins  = [c0,c1,c2]
    , outs = [q0,q1]
    }

-- Small adder

{--
as = 3 bit number
bs = 3 bit number
ms = 2 bit number
as < ms
bs < ms
--}

add2 :: Integer -> Integer -> Integer -> ST s (Circuit s)
add2 a b m = do
  as <- newVars (fromInt 3 a)
  bs <- newVars (fromInt 3 b)
  op <- makeAdderMod 2 m as bs
  return $ Circuit
    { op   = op
    , ins  = as ++ bs
    , outs = bs
    }

testAdder :: Integer -> Integer -> Integer -> Integer
testAdder a b m = runST $ do
  c <- add2 a b m
  res <- evalCircuit c Forward
  return (valuesToInt res)
    
-- a^x mod m
-- if we treat a^x mod m as a black box we don't really get anything
-- from symbolic (retrodictive) evaluation

expm :: Int -> Integer -> Integer -> ST s (Circuit s)
expm n a m = do
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" (n+1)
  ts <- newVars (fromInt (n+1) 1)
  us <- newVars (fromInt (n+1) 0)
  op <- makeExpMod n a m xs ts us
  return $ Circuit
    { op   = op
    , ins  = xs
    , outs = if odd n then ts else us
    }
                
runExpm :: Int -> Integer -> Integer -> Integer -> Integer
runExpm n a m x = runST $ do
  c <- expm n a m 
  updateVarsB (ins c) (fromInt (n+1) x)
  evalCircuit c Forward
  res <- mapM readSTRef (outs c)
  return (valuesToInt res)

symbolicRunExpm :: Int -> Integer -> Integer -> [Formula]
symbolicRunExpm n a m = runST $ do
  c <- expm n a m
  evalCircuit c Forward

retrodictiveRunExpm :: Int -> Integer -> Integer -> Integer -> [Formula]
retrodictiveRunExpm n a m res = runST $ do
  c <- expm n a m 
  updateVarsB (outs c) (fromInt (n+1) res)
  evalCircuit c Backward
  mapM readSTRef (outs c)

-- Grover (2x2 Sudoku example)
-- v0 = 0; v3 = 1 => no solutions
-- v0 = 0; v3 = 0 => not (v1v2)

grover :: ST s (Circuit s)
grover =  do
  vs <- newVars (fromInt 4 0)
  cs <- newVars (fromInt 4 0)
  out <- newVar True
  let op = S.fromList [
        cx (vs !! 0) (cs !! 0), 
        cx (vs !! 1) (cs !! 0), 
        cx (vs !! 0) (cs !! 1), 
        cx (vs !! 2) (cs !! 1), 
        cx (vs !! 1) (cs !! 2), 
        cx (vs !! 3) (cs !! 2), 
        cx (vs !! 2) (cs !! 3), 
        cx (vs !! 3) (cs !! 3),
        GToffoli 
        [True,True,True,True]
        [cs !! 0, cs !! 1, cs !! 2, cs !! 3]
        out,
        cx (vs !! 0) (cs !! 0), 
        cx (vs !! 1) (cs !! 0), 
        cx (vs !! 0) (cs !! 1), 
        cx (vs !! 2) (cs !! 1), 
        cx (vs !! 1) (cs !! 2), 
        cx (vs !! 3) (cs !! 2), 
        cx (vs !! 2) (cs !! 3), 
        cx (vs !! 3) (cs !! 3)]
  return $ Circuit
    { op   = op
    , ins  = vs ++ cs
    , outs = [out]
    }

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
