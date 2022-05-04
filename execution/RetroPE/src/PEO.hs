module PEO (run) where

import Data.STRef (readSTRef, writeSTRef)
import Data.List (partition, subsequences)
import qualified Data.MultiSet as MS
import qualified Data.Sequence as S
import Data.Bits ((.|.))

import Control.Monad.ST (ST)

import Text.Printf (printf)

import Value (Value(..))
import GToffoli (GToffoli(..), showGToffoli)
import Circuits (OP, Circuit(op))
import Trace (traceM)
import qualified FormAsBitmaps as FB

------------------------------------------------------------------------------
-- This is like PE but optimized for working in a very particular
-- representation.

peG :: GToffoli s FB.Formula -> ST s ()
peG g@(GToffoli bs cs t) = do
  msg <- showGToffoli g
  traceM (printf "Interpreting %s\n" msg) 
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  -- all the controls ought to be single literals
  let ctrl = map (FB.lits . MS.findMin . FB.ands) controls
  let r = sxor tv (normalize bs ctrl)
  traceM (printf "\tWriting %s\n" (show r)) 
  writeSTRef t r
  
pe :: OP s FB.Formula -> ST s ()
pe = foldMap peG

run :: Circuit s FB.Formula -> ST s ()
run circ = pe $ S.reverse (op circ)

-- We know a lot more when doing expansion of a single gate.
-- Rather than wait for 'downstream' to compute it all, just do it here.

normalize :: [Bool] -> [FB.Literal] -> FB.Formula
normalize bs cs = res
  where
    -- pair up the bools and variables, then partition
    -- 'same' are for straight-through variables,
    -- 'nega' for the negated ones
    pairs = zip bs cs
    part = partition fst pairs
    same :: FB.Literal
    same = foldr (.|.) 0 $ map snd $ fst part
    nega :: [ FB.Literal ]
    nega = map snd $ snd part
    -- nega' is then all the subsequences (aka powerset)
    nega' :: [[ FB.Literal ]]
    nega' = subsequences nega
    -- then prepend all the 'same' variables
    res' :: [FB.Ands]
    res' = map (\x -> FB.Ands $ same .|. (foldr (.|.) 0 x)) nega'
    -- and finally, make a big xor
    res :: FB.Formula
    res = FB.Formula $ MS.fromList res'
------------------------------------------------------------------------------
