module EvalZ where

import Data.STRef (readSTRef, writeSTRef)

import Control.Monad (when)
import Control.Monad.ST (ST, runST)

import Value (Value(..))
import Variable (Var)
import GToffoli (GToffoli(GToffoli))
import Circuits (OP, Circuit(op))

------------------------------------------------------------------------------
-- Evaluate a circuit in the Z basis (the computational basis)

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

------------------------------------------------------------------------------
-- Interpreter

controlsActive :: [Bool] -> [ZValue] -> Bool
controlsActive bs cs = and (zipWith (\ b (ZValue b') -> b == b') bs cs)

interpGT :: GToffoli (Var s ZValue) -> ST s ()
interpGT (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  when (controlsActive bs controls) $ writeSTRef t (snot tv)

interp :: OP (Var s ZValue) -> ST s ()
interp = foldMap interpGT

run :: Circuit s ZValue -> ST s ()
run = interp . op
 
------------------------------------------------------------------------------
