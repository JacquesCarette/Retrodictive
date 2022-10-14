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
-- Use Bool directly as the type.

------------------------------------------------------------------------------
-- Interpreter

controlsActive :: [Bool] -> [Bool] -> Bool
controlsActive bs cs = and (zipWith (==) bs cs)

interpGT :: GToffoli (Var s Bool) -> ST s ()
interpGT (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  when (controlsActive bs controls) $ writeSTRef t (snot tv)

interp :: OP (Var s Bool) -> ST s ()
interp = foldMap interpGT

run :: Circuit s Bool -> ST s ()
run = interp . op
 
------------------------------------------------------------------------------
