module Printing.GToffoli where

import Control.Monad.ST (ST)
import Data.STRef (readSTRef)

import Text.Printf (printf)

import GToffoli (GToffoli(GToffoli))

------------------------------------------------------------------------------
-- Printing Toffoli gates

showGToffoli :: Show v => GToffoli s v -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %s %s (%s)\n"
    (show (map fromEnum bs))
    (show controls)
    (show vt)

------------------------------------------------------------------------------
