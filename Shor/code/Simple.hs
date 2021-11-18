{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module Simple where

import Control.Monad.ST
import Control.Lens hiding (op,(:<),simple)
import Data.STRef
import qualified Data.Sequence as S
import Data.Sequence ((><))
import Text.Printf

import Experiment

----------------------------------------------------------------------------------------

simple :: Integer -> ST s (OP s,[Var s],[Var s])
simple c = do
  [c0,c1,c2] <- newVars "c" 0 (fromInt 3 c)
  q0 <- newVar "q" "0" False
  q1 <- newVar "q" "1" False
  let op = S.fromList
        [ cx "simple" c2 q1
        , cx "simple" c1 q1
        , cx "simple" q1 q0
        , ccx "simple" c1 q0 q1
        , cx "simple" q1 q0
        , xop "simple" q1
        , ccx "simple" c0 q1 q0
        , xop "simple" q1
        , cx "simple" q1 q0
        , ccx "simple" c0 q0 q1
        , cx "simple" q1 q0        
        ]
  return  (op,[c0,c1,c2],[q0,q1])

runSimple :: Integer -> (Integer,Integer)
runSimple c = runST $ do
  (op,cs,qs) <- simple c
  interpOP op
  cvs <- mapM readSTRef cs
  qvs <- mapM readSTRef qs
  return (toInt (map (\v -> toBool (v^.current)) cvs),
          toInt (map (\v -> toBool (v^.current)) qvs))

showSimple :: String
showSimple = runST $ do
  (op,cs,qs) <- simple 0
  writeSTRef (cs !! 0) (newDynValue "c" "0" "c0")
  writeSTRef (cs !! 1) (newDynValue "c" "1" "c1")
  writeSTRef (cs !! 2) (newDynValue "c" "2" "c2")
  writeSTRef (qs !! 0) (newDynValue "q" "0" "q0")
  writeSTRef (qs !! 1) (newDynValue "q" "1" "q1")
  showOP op

retroSimple :: Integer -> String
retroSimple q = runST $ do
  (op,cs,qs) <- simple 0
  writeSTRef (cs !! 0) (newDynValue "c" "0" "c0")
  writeSTRef (cs !! 1) (newDynValue "c" "1" "c1")
  writeSTRef (cs !! 2) (newDynValue "c" "2" "c2")
  let [q0,q1] = fromInt 2 q
  writeSTRef (qs !! 0) (newValue "q" "0" q0)
  writeSTRef (qs !! 1) (newValue "q" "1" q1)
  peOP (S.reverse op)
  cvs <- mapM readSTRef cs
  qvs <- mapM readSTRef qs
  return (show cvs ++ show qvs)


{--

*Simple> retroSimple 1

  q0 = 1 + c0 + c1 = 0
  q1 = c0 + c2     = 0

  c0 = 0, c1 = 1, c2 = 0  ==> c = 2
  c0 = 1, c1 = 0, c2 = 1  ==> c = 5

--}
  
----------------------------------------------------------------------------------------

