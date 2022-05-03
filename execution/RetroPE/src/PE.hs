module PE (run) where

import Data.STRef (readSTRef, writeSTRef)
import qualified Data.Sequence as S

import Control.Monad.ST (ST)

import Text.Printf (printf)

import Value (Value(..))
import GToffoli (GToffoli(..), showGToffoli)
import Circuits (OP, Circuit(op))
import Trace (traceM)

------------------------------------------------------------------------------
-- Evaluate a circuit with symbolic values (partial evaluation)

peG :: Value v => GToffoli s v -> ST s ()
peG g@(GToffoli bs cs t) = do
  msg <- showGToffoli g
  traceM (printf "Interpreting %s\n" msg) 
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  let funs = map (\b -> if b then id else snot) bs
  let r = sxor tv (snand (zipWith ($) funs controls))
  traceM (printf "\tWriting %s\n" (show r)) 
  writeSTRef t r
  
pe :: Value v => OP s v -> ST s ()
pe = foldMap peG

run :: Value v => Circuit s v -> ST s ()
run circ = pe $ S.reverse (op circ)

------------------------------------------------------------------------------
