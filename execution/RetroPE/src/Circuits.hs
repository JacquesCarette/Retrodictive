module Circuits where

import qualified Data.Sequence as S
import Data.Sequence (Seq)

import Variable (Var)
import GToffoli (GToffoli(GToffoli))
import Printing.GToffoli (showGToffoli)

------------------------------------------------------------------------------
-- Circuits manipulate locations holding (abstract) values

-- A circuit is a sequence of generalized Toffoli gates

type OP br = Seq (GToffoli br)

------------------------------------------------------------------------------
-- Combinators to grow circuits

cop :: br -> OP br -> OP br
cop c = fmap (\ (GToffoli bs cs t) -> GToffoli (True:bs) (c:cs) t)
  
ncop :: br -> OP br -> OP br
ncop c = fmap (\ (GToffoli bs cs t) -> GToffoli (False:bs) (c:cs) t)

ccop :: OP br -> [br] -> OP br
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
  { op          :: OP (Var s v)
  , xs          :: [Var s v]
  , ancillaIns  :: [Var s v]
  , ancillaOuts :: [Var s v]  
  , ancillaVals :: [v]
  }

------------------------------------------------------------------------------


