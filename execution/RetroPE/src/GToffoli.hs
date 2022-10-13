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
-- Basic gates

xop :: Var s v -> GToffoli s v
xop = GToffoli [] []

cx :: Var s v -> Var s v -> GToffoli s v
cx a = GToffoli [True] [a]

ncx :: Var s v -> Var s v -> GToffoli s v
ncx a = GToffoli [False] [a]

ccx :: Var s v -> Var s v -> Var s v -> GToffoli s v
ccx a b = GToffoli [True,True] [a,b]

cncx :: Var s v -> Var s v -> Var s v -> GToffoli s v
cncx a b = GToffoli [True,False] [a,b]

------------------------------------------------------------------------------
