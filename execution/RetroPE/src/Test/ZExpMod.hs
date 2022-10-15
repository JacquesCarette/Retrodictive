module Test.ZExpMod where

import Data.STRef (readSTRef, writeSTRef)

import Control.Monad.ST (runST)

import Text.Printf (printf)

import Circuits (Circuit(..))
import Printing.Circuits (showSizes, sizeOP)
import ArithCirc (expm)
import Value (fromInt)
import BoolUtils (toInt)
import EvalZ (run)

------------------------------------------------------------------------------
-- Test: run expm, in the Z basis.

runExpMod :: Int -> Integer -> Integer -> Integer -> IO ()
runExpMod n a m x = printResult $ runST $ do
  circ <- expm n a m
  mapM_ (uncurry writeSTRef) (zip (ancillaIns circ) (ancillaVals circ))
  mapM_ (uncurry writeSTRef) (zip (xs circ) (fromInt (n+1) x))
  run circ
  result <- mapM readSTRef (ancillaOuts circ)
  return (toInt result, showSizes (sizeOP (op circ)))
  where printResult (res,size) = do
          putStrLn size
          putStrLn (printf "Result = %d" res)

------------------------------------------------------------------------------

