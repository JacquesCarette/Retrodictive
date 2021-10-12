{-# LANGUAGE TemplateHaskell #-}

-- Ref:
-- Quantum Networks for Elementary Arithmetic Operations
-- Vlatko Vedral∗, Adriano Barenco and Artur Ekert

module Shor where

import Data.Char
import GHC.Integer.GMP.Internals
import Data.Vector (Vector, fromList, toList, (!), (//))
import qualified Data.Vector as V 

import Text.Printf
import Test.QuickCheck
import Control.Exception.Assert

import qualified Debug.Trace

-- Toggle 

debug = False
--debug = True

trace :: String -> a -> a
trace s a = if debug then Debug.Trace.trace s a else a

------------------------------------------------------------------------------
-- Abstract operations to be given either a conventional semantics or
-- a symbolic one

type Var = Int

data Bit = Bool Bool | BitVar Var | NotBitVar Var deriving (Eq,Show)

class Monad m => Circuit m where
  cx   :: (Bit,Bit) -> m (Bit,Bit)
  ccx  :: (Bit,Bit,Bit) -> m (Bit,Bit,Bit)

-- Is there an elegant way to invert circuits???

invert :: Circuit m => (a -> m b) -> b -> m a
invert f out = undefined

------------------------------------------------------------------------------
-- Standard interpreter

data Std a = Std a

simulate :: Std a -> a
simulate (Std a) = a

instance Functor Std where
  fmap f (Std a) = Std (f a)

instance Applicative Std where
  pure = Std
  (Std f) <*> (Std a) = Std (f a)

instance Monad Std where
  return = Std
  (Std e1) >>= e2 = e2 e1

instance Circuit Std where
  cx arg@(Bool ctrl, Bool target)
    | ctrl = return (Bool ctrl, Bool (not target))
    | otherwise = return arg

  ccx arg@(Bool ctrl1, Bool ctrl2, Bool target)
    | ctrl1 && ctrl2 = return (Bool ctrl1, Bool ctrl2, Bool (not target))
    | otherwise = return arg

------------------------------------------------------------------------------
-- Partial evaluator

------------------------------------------------------------------------------
-- Actual circuits

sumOP :: Circuit m => (Bit,Bit,Bit) -> m (Bit,Bit,Bit)
sumOP (c,a,b) =
  do (a,b) <- cx (a,b)
     (c,b) <- cx (c,b)
     return (c,a,b)

carryOP :: Circuit m => (Bit,Bit,Bit,Bit) -> m (Bit,Bit,Bit,Bit)
carryOP (c,a,b,c') =
  do (a,b,c') <- ccx (a,b,c')
     (a,b) <- cx (a,b)
     (c,b,c') <- ccx (c,b,c')
     return (c,a,b,c')


------------------------------------------------------------------------------
-- Testing...

test :: (Bit,Bit,Bit)
test = simulate $ sumOP (Bool True, Bool False, Bool False)

------------------------------------------------------------------------------
------------------------------------------------------------------------------
