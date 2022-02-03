module QAlgos where

import Data.STRef (readSTRef,writeSTRef)
import Data.List (intercalate,group,sort)

import Control.Monad.ST (runST)

import System.Random (randomRIO)

import Text.Printf (printf)

import Value (Var, Value(..), newVar, newVars, fromInt)
import Circuits (Circuit(..), showSizes, sizeOP)
import ArithCirc (expm)
import PE (run)
import Synthesis (synthesis)
import FormulaRepr (FormulaRepr(..))

----------------------------------------------------------------------------------------
-- Some quantum algorithms

-- Retrodictive execution of Shor's algorithm

peExpMod :: (Show f, Value f) 
         => FormulaRepr f -> Int -> Integer -> Integer -> Integer -> IO ()
peExpMod fr n a m r = printResult $ runST $ do
  circ <- expm n a m
  mapM_ (uncurry writeSTRef) (zip (ancillaOuts circ) (fromInt (n+1) r))
  mapM_ (uncurry writeSTRef) (zip (xs circ) (fromVars fr (n+1) "x"))
  run circ
  result <- mapM readSTRef (ancillaIns circ)
  let eqs = zip result (ancillaVals circ)
  return (eqs, showSizes (sizeOP (op circ)))
  where printResult (eqs,size) = do
          putStrLn size
          mapM_ (\(r,v) ->
            let sr = show r
                sv = show v
            in if sr == sv then return () else 
              printf "%s = %s\n" sr sv)
            eqs

retroShor :: (Show f, Value f) => FormulaRepr f -> Integer -> IO ()
retroShor fr m = do
      a <- randomRIO (2,m-1)
      let n = ceiling $ logBase 2 (fromInteger m * fromInteger m)
      let gma = gcd m a 
      if gma /= 1 
        then putStrLn (printf "Lucky guess %d = %d * %d\n" m gma (m `div` gma))
        else do putStrLn (printf "n=%d; a=%d\n" n a)
                peExpMod fr n a m 1

-- Deutsch

deutschId, deutschNot, deutsch0, deutsch1 :: [Bool] -> [Bool]
deutschId [x,y]  = [x,y /= x]
deutschNot [x,y] = [x,y /= not x]
deutsch0 [x,y]   = [x,y]
deutsch1 [x,y]   = [x,not y]

retroDeutsch :: (Show f, Value f) => FormulaRepr f -> ([Bool] -> [Bool]) -> IO ()
retroDeutsch fr f = print $ runST $ do
  x <- newVar (fromVar fr "x")
  y <- newVar zero
  run Circuit { op = synthesis 2 [x,y] f
              , xs = [x]
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

{--

*PEZ> retroDeutsch deutschId
x

*PEZ> retroDeutsch deutschNot
1 + x

*PEZ> retroDeutsch deutsch0
0

*PEZ> retroDeutsch deutsch1
1

--}

retroDeutschJozsa :: (Show f, Value f) 
                   => FormulaRepr f -> Int -> ([Bool] -> [Bool]) -> IO ()
retroDeutschJozsa fr n f = printResult $ runST $ do
  xs <- newVars (fromVars fr n "x")
  y <- newVar zero
  run Circuit { op = synthesis (n+1) (xs ++ [y]) f
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y
  where printResult yv = print yv

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
