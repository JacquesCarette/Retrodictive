module Value where

import Control.Monad.ST (ST)
import Data.STRef (STRef, newSTRef)

----------------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

class (Show v, Enum v) => Value v where
  zero :: v
  one  :: v
  snot :: v -> v
  sand :: v -> v -> v
  sxor :: v -> v -> v

instance Value Bool where
  zero = False
  one  = True
  snot = not
  sand = (&&)
  sxor = (/=)

bin :: Value v => Integer -> [v]
bin n | n < 0 = error "Panic: (bin) Integer is negative!"
bin 0 = []
bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q

-- fromInt takes an Integer and pads it out (on the right) with zeros so that
-- the result is |len| long.
fromInt :: Value v => Int -> Integer -> [v]
fromInt len n
  | len < 0 = error "Panic: (fromInt) trying to truncate?"
  | l < 0 = error "Panic: (fromInt) asking for negative number of bits"
  | otherwise = bits ++ replicate (len - length bits) zero
  where
      bits = bin n
      l = len - length bits

type Var s v = STRef s v

newVar :: Value v => v -> ST s (Var s v)
newVar = newSTRef

newVars :: Value v => [v] -> ST s [Var s v]
newVars = mapM newVar

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
