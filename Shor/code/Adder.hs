{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module Adder where

import Control.Monad.ST
import Control.Lens hiding (op,(:<))
import Data.STRef
import qualified Data.Sequence as S
import Data.Sequence ((><))
import Text.Printf

import Experiment

----------------------------------------------------------------------------------------

add2Eval :: Integer -> Integer -> Integer -> Integer
add2Eval a b m = runST $ do
  as <- newVars "a" 0 (fromInt 3 a)
  bs <- newVars "b" 0 (fromInt 3 b)
  op <- makeAdderMod 2 m as bs
  interpOP op
  bvs <- mapM readSTRef bs
  return (toInt (map (\v -> toBool (v^.current)) bvs))

{--
as = 3 bit number
bs = 3 bit number
ms = 2 bit number
as < ms
bs < ms

Inputs: as, bs, ms
Output: bs

*Adder> [ add2Eval a b 3 | a <- [0..2], b <- [0..2]]
[0,1,2,1,2,0,2,0,1]
--}

add2Circuit :: String
add2Circuit = runST $ do
  gensym <- newSTRef 0
  as <- newDynVars gensym "a" 3
  writeSTRef gensym 0
  bs <- newDynVars gensym "b" 3
  op <- makeAdderMod 2 3 as bs
  op <- simplifyOP op
  sh <- showOP op
  let dec =
        "qreg a[3];\n" ++
        "qreg b[3];\n" ++
        "qreg m[2];\n" ++
        "qreg d[2];\n" ++
        "qreg e[1];\n" ++
        "qreg c[6];\n" ++
        "\n\n" ++
        "reset c[1];\n" ++
        "reset c[3];\n" ++
        "reset e[0];\n" ++
        "reset m[0];\nx m[0];\n" ++
        "reset m[1];\nx m[1];\n" ++
        "\n\n"
  return (dec ++ sh)

-- Inputs that produce result (b) = 1
-- a1 a0 arbitrary
-- b0 = 1 + a0 + a1
-- b1 = a1 + a0a1 
-- b2 = 0


add2Retro :: Integer -> String 
add2Retro b = runST $ do
  gensym <- newSTRef 0
  as <- newDynVars gensym "a" 3
  bs <- newVars "b" 0 (fromInt 3 b)
  op <- makeAdderMod 2 3 as bs
  peOP (S.reverse op)
  bsv <- mapM readSTRef bs
  return (show bsv)

add2sum1Eval :: Integer -> Integer
add2sum1Eval a = runST $ do
  gensym <- newSTRef 0
  [a0,a1,a2] <- newVars "a" 0 (fromInt 3 a)
  [b0,b1,b2] <- newVars "b" 0 (fromInt 3 0)
  bop <- makeAdderMod 2 3 [a0,a1,a2] [b0,b1,b2]
  let op =
        S.singleton (cx "add" a0 b0) ><
        S.singleton (cx "add" a1 b0) ><
        S.singleton (xop "add" b0) ><
        S.singleton (cx "add" a1 b1) ><
        S.singleton (ccx "add" a0 a1 b1) ><
        bop
  interpOP op
  bvs <- mapM readSTRef [b0,b1,b2]
  return (toInt (map (\v -> toBool (v^.current)) bvs))

add2sum1 :: String 
add2sum1 = runST $ do
  gensym <- newSTRef 0
  [a0,a1,a2] <- newDynVars gensym "a" 3
  [b0,b1,b2] <- newVars "b" 0 (fromInt 3 0)
  bop <- makeAdderMod 2 3 [a0,a1,a2] [b0,b1,b2]  
  let op =
        S.singleton (cx "add" a0 b0) ><
        S.singleton (cx "add" a1 b0) ><
        S.singleton (xop "add" b0) ><
        S.singleton (cx "add" a1 b1) ><
        S.singleton (ccx "add" a0 a1 b1) ><
        bop
  op <- simplifyOP op        
  showOP op
  
----------------------------------------------------------------------------------------

