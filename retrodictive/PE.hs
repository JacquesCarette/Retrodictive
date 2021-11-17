{-# LANGUAGE MultiWayIf #-}

module PE where

import Control.Monad 
import Control.Monad.ST
import Control.Lens hiding (op,(:<))

import qualified Data.Sequence as S
import Data.List (nub)
import Data.STRef

import Text.Printf (printf)

--

import Debug
import Numeric
import ANF
import Circuit

----------------------------------------------------------------------------------------
-- Phase to deal with all statically known gates

restoreSaved :: GToffoli s -> ST s (GToffoli s)
restoreSaved g@(GToffoli ctx bsOrig csOrig t) = do
  vt <- readSTRef t
  maybe
    (return ()) 
    (\vs -> writeSTRef t (set saved Nothing $ set current (fromBool vs) vt))
    (vt^.saved)
  return g

shrinkControls :: [Bool] -> [Var s] -> [Value] -> ([Bool],[Var s],[Value])
shrinkControls [] [] [] = ([],[],[])
shrinkControls (b:bs) (c:cs) (v:vs)
  | isStatic (v^.current) && toBool (v^.current) == b = shrinkControls bs cs vs
  | otherwise =
    let (bs',cs',vs') = shrinkControls bs cs vs
    in (b:bs',c:cs',v:vs')

simplifyG :: GToffoli s -> ST s (OP s)
simplifyG (GToffoli ctx bsOrig csOrig t) = do
  controlsOrig <- mapM readSTRef csOrig
  vt <- readSTRef t
  let (bs,cs,controls) = shrinkControls bsOrig csOrig controlsOrig
  let ca = controlsActive bs controls
  if | ca == Just True && isStatic (vt^.current) -> do
         writeSTRef t (vnot vt)
         return S.empty
     | ca == Just False ->
         return S.empty
     | otherwise -> do
         -- save value of target; mark it as unknown for remainder of phase
         when (vt^.saved == Nothing && isStatic (vt^.current)) $
           writeSTRef t
           (set current (fromVar "_") $ 
             set saved (Just $ toBool (vt^.current)) vt)
         return $ S.singleton (GToffoli ctx bs cs t)

simplifyOP :: OP s -> ST s (OP s)
simplifyOP op = do
  op <- foldMap simplifyG op
  mapM restoreSaved op

----------------------------------------------------------------------------------------
-- Phase to run symbolically generating formulae instead of values
-- ---------------------------------------------------------------

specialCases :: [Bool] -> [Var s] -> Var s -> [Value] -> Value -> ST s ()
specialCases [b] [cx] tx [x] y =
  let fc = if b then x^.current else snot (x^.current)
      fs = sxor fc (y^.current)
  in writeSTRef tx $ set current fs y
specialCases [b1,b2] [cx1,cx2] tx [x1,x2] y = 
  let cfs = sand
            (if b1 then x1^.current else snot (x1^.current))
            (if b2 then x2^.current else snot (x2^.current))
      tfs = sxor cfs (y^.current)
  in writeSTRef tx $ set current tfs y
specialCases [b1,b2,b3,b4] [cx1,cx2,cx3,cx4] tx [x1,x2,x3,x4] y = 
  let cfs = sand
            (if b1 then x1^.current else snot (x1^.current))
            (sand
             (if b2 then x2^.current else snot (x2^.current))
             (sand
              (if b3 then x3^.current else snot (x3^.current))
              (if b4 then x4^.current else snot (x4^.current))))
      tfs = sxor cfs (y^.current)
  in writeSTRef tx $ set current tfs y


peG :: GToffoli s -> ST s (OP s)
peG g@(GToffoli ctx bs' cs' t) = do
  controls' <- mapM readSTRef cs'
  tv <- readSTRef t
  let (bs,cs,controls) = shrinkControls bs' cs' controls'
  let ca = controlsActive bs controls
  if | ca == Just True -> do
         writeSTRef t (vnot tv)
         return S.empty
     | ca == Just False -> do
         return S.empty
     | otherwise -> do
         let gSimple = GToffoli ctx bs cs t
         d <- showGToffoli gSimple
         specialCases bs cs t controls tv
         return (S.singleton gSimple)

peOP :: OP s -> ST s (OP s)
peOP = foldMap peG

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

