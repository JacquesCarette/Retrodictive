module GToffoli where

import Control.Monad.ST (ST)
import Data.STRef (readSTRef)

import Text.Printf (printf)

import Variable (Var)

------------------------------------------------------------------------------
-- Generalized Toffoli gates

-- (Circuits will be made out of these)

data GToffoli s v = GToffoli [Bool] [Var s v] (Var s v)
  deriving Eq

showGToffoli :: Show v => GToffoli s v -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %s %s (%s)\n"
    (show (map fromEnum bs))
    (show controls)
    (show vt)

------------------------------------------------------------------------------
