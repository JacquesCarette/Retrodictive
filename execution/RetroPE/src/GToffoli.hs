module GToffoli where

import Prelude hiding (seq)

import Data.Maybe (catMaybes, maybe, fromMaybe, fromJust)
import Data.List (find,union,intercalate,delete,(\\),intersect,sort,nub)

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))

import Control.Lens hiding (op,(:<))
import Control.Monad 
import Control.Monad.ST
import Data.STRef

import System.Random (randomRIO)
import GHC.Integer.GMP.Internals (powModInteger)
  
import Text.Printf (printf)
import Test.QuickCheck hiding ((><))
import Control.Exception.Assert (assert, assertMessage)
import qualified Debug.Trace as Debug

import Numeric
import Value

----------------------------------------------------------------------------------------
-- Generalized Toffoli gates

-- (Circuits will be made out of these)

data GToffoli s v = GToffoli [Bool] [Var s v] (Var s v)
  deriving Eq

showGToffoli :: Value v => GToffoli s v -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %s %s (%s)\n"
    (show (map fromEnum bs))
    (show controls)
    (show vt)
