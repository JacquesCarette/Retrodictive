module Value where

import Control.Monad.ST (ST)
import Data.STRef (STRef, newSTRef)

------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

-- Values will have different representations that support symbolic
-- values: each representation must have implementations of zero, one,
-- negation, conjunction, and exlusive-or

class (Show v, Enum v) => Value v where
  zero :: v
  one  :: v
  snot :: v -> v
  sand :: v -> v -> v
  sxor :: v -> v -> v

  -- has a default implementation
  snand :: [v] -> v -- n-ary and
  snand = foldr sand one

-- The default implementation of value is Bool

instance Value Bool where
  zero = False
  one  = True
  snot = not
  sand = (&&)
  sxor = (/=)

-- Convert an integer to a sequence of booleans (or more generally a
-- sequence of abstract values)

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

-- Variables are locations holding values

type Var s v = STRef s v

newVar :: Value v => v -> ST s (Var s v)
newVar = newSTRef

newVars :: Value v => [v] -> ST s [Var s v]
newVars = mapM newVar

------------------------------------------------------------------------------

