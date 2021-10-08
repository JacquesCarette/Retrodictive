module ShorPE where

import Data.Vector

------------------------------------------------------------------------------

type W = Vector Bool

data Op = Swap Int Int 
        | (:.:) Op Op

interp :: Op -> W -> W
interp (Swap i j) w = w // [(i , w ! j), (j , w ! i)]
interp (op1 :.: op2) w = interp op2 (interp op1 w)

------------------------------------------------------------------------------
------------------------------------------------------------------------------