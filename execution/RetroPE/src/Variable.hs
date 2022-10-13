module Variable where

import Control.Monad.ST (ST)
import Data.STRef (STRef, newSTRef)

import Value (Value)

------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

-- Variables are locations holding values

type Var s v = STRef s v

newVar :: Value v => v -> ST s (Var s v)
newVar = newSTRef

newVars :: Value v => [v] -> ST s [Var s v]
newVars = mapM newVar

------------------------------------------------------------------------------

