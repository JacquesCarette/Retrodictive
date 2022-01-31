module Value where

import Prelude hiding (seq)
import Control.Monad.ST
import Data.STRef

----------------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

class (Show v, Enum v) => Value v where
  zero :: v
  one  :: v
  snot :: v -> v
  sand :: v -> v -> v
  sxor :: v -> v -> v

bin :: Value v => Integer -> [v]
bin 0 = []
bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q

fromInt :: Value v => Int -> Integer -> [v]
fromInt len n = bits ++ replicate (len - length bits) zero
  where bits = bin n

type Var s v = STRef s v

newVar :: Value v => v -> ST s (Var s v)
newVar = newSTRef

newVars :: Value v => [v] -> ST s [Var s v]
newVars = mapM newVar

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
