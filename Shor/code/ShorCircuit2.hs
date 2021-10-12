{-# LANGUAGE TemplateHaskell #-}

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

type Var = Int

data Bit = Bool Bool | BitVar Var | NotBitVar Var deriving (Eq,Show)

class Monad m => Circuit m where
  cx   :: (Bit,Bit) -> m (Bit,Bit)
  ccx  :: (Bit,Bit,Bit) -> m (Bit,Bit,Bit)

-- sum: c, a, b => c, a, (a+b+c) mod 2

sumOP :: Circuit m => (Bit,Bit,Bit) -> m (Bit,Bit,Bit)
sumOP (c,a,b) =
  do (a,b) <- cx (a,b)
     (c,b) <- cx (c,b)
     return (c,a,b)

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


test :: (Bit,Bit,Bit)
test = simulate $ sumOP (Bool True, Bool False, Bool False)


------------------------------------------------------------------------------
------------------------------------------------------------------------------
