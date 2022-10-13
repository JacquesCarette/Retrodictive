module Circuits where

import qualified Data.Sequence as S
import Data.Sequence (Seq)

import Control.Monad.ST (ST)

import Text.Printf (printf)

import Variable (Var)
import GToffoli (GToffoli(GToffoli), showGToffoli)

------------------------------------------------------------------------------
-- Circuits manipulate locations holding (abstract) values

-- A circuit is a sequence of generalized Toffoli gates

type OP s v = Seq (GToffoli s v)

showOP :: Show v => OP s v -> ST s String
showOP = foldMap showGToffoli

sizeOP :: OP s v -> [(Int,Int)]
sizeOP = foldr (\(GToffoli cs _ _) -> incR (length cs)) [] 
  where incR n [] = [(n,1)]
        incR n ((g,r):gs) | n == g = (g,r+1) : gs
                          | otherwise = (g,r) : incR n gs

showSizes :: [(Int,Int)] -> String
showSizes [] = ""
showSizes ((g,r) : gs) =
  printf "Generalized Toffoli Gates with %d controls = %d\n" g r
  ++ showSizes gs

------------------------------------------------------------------------------
-- Basic circuits

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

cop :: Var s v -> OP s v -> OP s v
cop c = fmap (\ (GToffoli bs cs t) -> GToffoli (True:bs) (c:cs) t)
  
ncop :: Var s v -> OP s v -> OP s v
ncop c = fmap (\ (GToffoli bs cs t) -> GToffoli (False:bs) (c:cs) t)

ccop :: OP s v -> [Var s v] -> OP s v
ccop = foldr cop

------------------------------------------------------------------------------
-- Circuit abstraction

{--

                -------------
       xs -----|             |----- xs
               |     op      | 
 ancillasIns --|             |----- ancillaOuts
                -------------
 
  ancillaVals 
    - to initialize ancillaIns in forward evaluation, or
    - to compare with result of retrodictive execution
 
  forward eval: set ancillaIns to ancillaVals; set xs to input; run;
  check ancillaOuts

  retrodictive: set xs to symbolic; set ancillaOuts to input; run;
  check ancillaIns against ancillaVals

--}

data Circuit s v = Circuit
  { op          :: OP s v
  , xs          :: [Var s v]
  , ancillaIns  :: [Var s v]
  , ancillaOuts :: [Var s v]  
  , ancillaVals :: [v]
  }

------------------------------------------------------------------------------


