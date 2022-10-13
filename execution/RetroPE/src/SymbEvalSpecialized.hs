module SymbEvalSpecialized (run) where

import Data.STRef (readSTRef, writeSTRef)
import qualified Data.MultiSet as MS
import qualified Data.Sequence as S

import Control.Monad.ST (ST)

import Text.Printf (printf)

import Value (Value(..))
import Variable (Var)
import GToffoli (GToffoli(..))
import Printing.GToffoli (showGToffoli)
import Circuits (OP, Circuit(op))
import Trace (traceM)
import qualified FormAsBitmaps as FB

------------------------------------------------------------------------------
-- This is like SymbEval but optimized for working in a very particular
-- representation, that of FormAsBitmaps

evalGates :: GToffoli (Var s FB.Formula) -> ST s ()
evalGates (GToffoli bs cs t) = do
  -- setup
  controls <- mapM readSTRef cs
  tv <- readSTRef t

  -- actually "run"
  let funs = map (\b -> if b then id else snot) bs
  let r = sxor tv (snand (zipWith ($) funs controls))

  -- all the controls ought to be single literals
  let ctrl = map (FB.lits . MS.findMin . FB.ands) controls
  let tv' = FB.ands $ tv
  let nc = FB.normalize bs ctrl
  let r = FB.xor tv' nc

  writeSTRef t r

evalGatesDebug :: GToffoli (Var s FB.Formula) -> ST s ()
evalGatesDebug g@(GToffoli bs cs t) = do
  -- debug
  msg <- showGToffoli g
  traceM (printf "Interpreting %s\n" msg) 

  -- run
  evalGates g
  r <- readSTRef t
  -- debug 
  traceM (printf "\tWriting %s\n" (show r)) 

run :: Circuit s FB.Formula -> ST s ()
run circ = foldMap evalGatesDebug $ S.reverse (op circ)

------------------------------------------------------------------------------

