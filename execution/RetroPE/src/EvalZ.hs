module EvalZ where

-- evaluate a circuit in the Z basis (the computational basis)

import Data.STRef
import Data.Maybe (catMaybes, maybe, fromMaybe, fromJust)

import Control.Monad 
import Control.Monad.ST

import Text.Printf

import GToffoli
import Circuits
import ArithCirc (expm)
import Value
import Numeric

----------------------------------------------------------------------------------------
-- Values

newtype ZValue = ZValue Bool

instance Enum ZValue where
  toEnum 0 = ZValue False
  toEnum 1 = ZValue True
  fromEnum (ZValue False) = 0
  fromEnum (ZValue True) = 1

instance Show ZValue where
  show (ZValue b) = show b

instance Value ZValue where
  zero = ZValue False
  one = ZValue True
  snot (ZValue b) = ZValue (not b)
  sand (ZValue b1) (ZValue b2) = ZValue (b1 && b2)
  sxor (ZValue b1) (ZValue b2) = ZValue (b1 /= b2)

----------------------------------------------------------------------------------------
-- Interpreter

controlsActive :: [Bool] -> [ZValue] -> Bool
controlsActive bs cs = and (zipWith (\ b (ZValue b') -> b == b') bs cs)

interpGT :: GToffoli s ZValue -> ST s ()
interpGT (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  when (controlsActive bs controls) $ writeSTRef t (snot tv)

interp :: OP s ZValue -> ST s ()
interp = foldMap interpGT

run :: Circuit s ZValue -> ST s ()
run = interp . op
 
----------------------------------------------------------------------------------------
-- Tests

runExpMod :: Int -> Integer -> Integer -> Integer -> IO ()
runExpMod n a m x = printResult $ runST $ do
  circ <- expm n a m
  mapM_ (uncurry writeSTRef) (zip (ancillaIns circ) (ancillaVals circ))
  mapM_ (uncurry writeSTRef) (zip (xs circ) (fromInt (n+1) x))
  run circ
  result <- mapM readSTRef (ancillaOuts circ)
  return (toInt (map (\ (ZValue b) -> b) result), showSizes (sizeOP (op circ)))
  where printResult (res,size) = do
          putStrLn size
          putStrLn (printf "Result = %d" res)

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
