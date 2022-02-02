module PE where

import Data.STRef
import Data.List (intercalate,group,sort)
import Data.Maybe (catMaybes, maybe, fromMaybe, fromJust)
import qualified Data.Sequence as S

import Control.Monad 
import Control.Monad.ST

import System.Random (randomRIO)

import Text.Printf

import Value
import Circuits
import Trace (traceM)

----------------------------------------------------------------------------------------
-- PE

peG :: Value v => GToffoli s v -> ST s ()
peG g@(GToffoli bs cs t) = do
  msg <- showGToffoli g
  traceM (printf "Interpreting %s\n" msg) 
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  let funs = map (\b -> if b then id else snot) bs
  let r = sxor tv (foldr sand one (zipWith ($) funs controls))
  traceM (printf "\tWriting %s\n" (show r)) 
  writeSTRef t r
  
pe :: Value v => OP s v -> ST s ()
pe = foldMap peG

run :: Value v => Circuit s v -> ST s ()
run circ = pe $ S.reverse (op circ)

----------------------------------------------------------------------------------------
