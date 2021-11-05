{-# LANGUAGE MultiWayIf #-}
--{-# LANGUAGE TemplateHaskell #-}

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
import ExpMod

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

simplifyCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
simplifyCircuit c = do
  simplified <- simplifyOP $ c^.circ
  return (set circ simplified c)

----------------------------------------------------------------------------------------
-- Phase to run symbolically generating formulae instead of values
-- ---------------------------------------------------------------

specialCases :: String -> [Bool] -> [Var s] -> Var s -> [Value] -> Value -> ST s ()
specialCases msg [b] [cx] tx [x] y =
  let fc = if b then x^.current else snot (x^.current)
      fs = sxor fc (y^.current)
  in  do traceM (printf "%s ==> %s" msg (show fs))
         writeSTRef tx $ set current fs y
specialCases msg [b1,b2] [cx1,cx2] tx [x1,x2] y = 
  let cfs = sand
            (if b1 then x1^.current else snot (x1^.current))
            (if b2 then x2^.current else snot (x2^.current))
      tfs = sxor cfs (y^.current)
  in do traceM (printf "%s ==> %s" msg (show tfs))
        writeSTRef tx $ set current tfs y
specialCases msg bs cs t controls vt = do
  error (printf "%s (Toffoli 4 or more)" msg)

peG :: Int -> (GToffoli s, Int) -> ST s (OP s)
peG size (g@(GToffoli ctx bs' cs' t), count) = do
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
         let msg = printf "\nProcessing gate %d of %d:\n\n\t%s" count size d
         specialCases msg bs cs t controls tv
         return (S.singleton gSimple)

peCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
peCircuit c = do
  c <- simplifyCircuit c
  let size = S.length (c^.circ)
  op' <- foldMap (peG size) $ S.zip (c^.circ) (S.fromFunction size (+1))
  return $ set circ op' c

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Making and executing circuits

runPE :: Int -> Integer -> Integer -> Integer -> IO ()
runPE n a m res = pretty $ runST $ do
  circuit <- makeInvExpMod n a m res 
  circuit <- peCircuit circuit
  ts <- mapM readSTRef (circuit^.ts)
  us <- mapM readSTRef (circuit^.us)
  return (zip ts (fromInt (n+1) 1), zip us (fromInt (n+1) 0))
  where
    trueEq (v,b) = isStatic (v^.current) && toBool (v^.current) == b
    
    pretty (ts',us') = do
      putStrLn (take 50 (repeat '_'))
      let ts = filter (not . trueEq) (nub ts')
      let us = filter (not . trueEq) (nub us')
      unless (null ts)
        (mapM_ (\(v,b) -> printf "%s = %s\n" (show v) (if b then "1" else "0")) ts)
      unless (null us)
        (mapM_ (\(v,b) -> printf "%s = %s\n" (show v) (if b then "1" else "0")) us)
      putStrLn (take 50 (repeat '_'))

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

