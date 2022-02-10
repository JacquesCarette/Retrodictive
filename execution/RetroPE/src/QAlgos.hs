{-# LANGUAGE ViewPatterns #-}

module QAlgos where

import Data.STRef (readSTRef,writeSTRef)
import Data.List (intercalate,group,sort)

import Control.Monad.ST (runST)

import System.Random (randomRIO)

import Numeric (readHex)
import GHC.Show (intToDigit)
import Text.Printf (printf)

import Value (Var, Value(..), newVar, newVars, fromInt)
import Circuits (Circuit(..), showSizes, sizeOP)
import ArithCirc (expm)
import PE (run)
import Synthesis (synthesis)
import FormulaRepr (FormulaRepr(..))
import QNumeric (toInt)

----------------------------------------------------------------------------------------
-- Some quantum algorithms

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

-- Deutsch Jozsa

viewL :: [a] -> ([a],a)
viewL xs = (init xs, last xs)

uf :: ([Bool] -> Bool) -> ([Bool] -> [Bool])
uf f (viewL -> (xs,y)) = xs ++ [f xs /= y]

deutschJozsaConstant0, deutschJozsaConstant1 :: [Bool] -> [Bool]
deutschJozsaBal1, deutschJozsaBal2, deutschJozsaBal3 :: [Bool] -> [Bool]
-- f(x) = 0
deutschJozsaConstant0 = uf (const False)
-- f(x) = 1
deutschJozsaConstant1 = uf (const True)
-- f(x0x1x2..) = x0
deutschJozsaBal1 = uf head
-- f(x0x1x2..) = xor(x0,x1,x2...)
deutschJozsaBal2 = uf (foldr (/=) False)
-- Example 1 from https://ajc.maths.uq.edu.au/pdf/29/ajc_v29_p231.pdf
-- n=6; output in hex 04511b5e37e23e6d
deutschJozsaBal3 = uf f
  where shex = "04511b5e37e23e6d"
        h2Int :: Char -> Int
        h2Int c = fst (head (readHex [c]))
        h2Str :: Char -> String
        h2Str c = printf "%04b" (h2Int c)
        sbin :: [Bool]
        sbin = map (\c -> if c == '0' then False else True) $ concatMap h2Str shex
        f xs = sbin !! fromInteger (toInt xs)

retroDeutschJozsa :: (Show f, Value f) 
                   => FormulaRepr f -> Int -> ([Bool] -> [Bool]) -> IO ()
retroDeutschJozsa fr n f = print $ runST $ do
  xs <- newVars (fromVars fr n "x")
  y <- newVar zero
  run Circuit { op = synthesis (n+1) (xs ++ [y]) f
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

-- Shor

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

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
