module SymbEval (run) where

import Data.STRef (readSTRef, writeSTRef)
import qualified Data.Sequence as S

import Control.Monad.ST (ST)

import Text.Printf (printf)

import Value (Value(snot,sxor,snand))
import Variable (Var)
import GToffoli (GToffoli(..))
import Printing.GToffoli (showGToffoli)
import Circuits (OP, Circuit(op))
import Trace (traceM)

------------------------------------------------------------------------------
-- Evaluate a circuit with symbolic values (aka symbolic evaluation)

evalGates :: Value v => GToffoli (Var s v) -> ST s ()
evalGates (GToffoli bs cs t) = do
  -- setup
  controls <- mapM readSTRef cs
  tv <- readSTRef t

  -- actually "run"
  let funs = map (\b -> if b then id else snot) bs
  let r = sxor tv (snand (zipWith ($) funs controls))

  writeSTRef t r

evalGatesDebug :: Value v => GToffoli (Var s v) -> ST s ()
evalGatesDebug g@(GToffoli bs cs t) = do
  -- debug
  msg <- showGToffoli g
  traceM (printf "Interpreting %s\n" msg) 

  evalGates g
  r <- readSTRef t
  -- debug 
  traceM (printf "\tWriting %s\n" (show r)) 
  
run :: Value v => Circuit s v -> ST s ()
run circ = foldMap evalGates $ S.reverse (op circ)

------------------------------------------------------------------------------
