module Printing.Circuits where

import Control.Monad.ST (ST)
import Text.Printf (printf)

import Variable (Var)
import Circuits (OP)
import GToffoli (GToffoli(GToffoli))
import Printing.GToffoli (showGToffoli)

------------------------------------------------------------------------------
-- Functions for printing of circuits

showOP :: Show v => OP (Var s v) -> ST s String
showOP = foldMap showGToffoli

sizeOP :: OP br -> [(Int,Int)]
sizeOP = foldr (\(GToffoli cs _ _) -> incR (length cs)) [] 
  where incR n [] = [(n,1)]
        incR n ((g,r):gs) | n == g = (g,r+1) : gs
                          | otherwise = (g,r) : incR n gs

showSizes :: [(Int,Int)] -> String
showSizes [] = ""
showSizes ((g,r) : gs) =
  printf "Generalized Toffoli Gates with %d controls = %d\n" g r
  ++ showSizes gs
