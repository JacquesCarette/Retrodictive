module GToffoli where

------------------------------------------------------------------------------
-- Generalized Toffoli gates

-- (Circuits will be made out of these)

data GToffoli br = GToffoli [Bool] [br] br

------------------------------------------------------------------------------
-- Basic gates

xop :: br -> GToffoli br
xop = GToffoli [] []

cx :: br -> br -> GToffoli br
cx a = GToffoli [True] [a]

ncx :: br -> br -> GToffoli br
ncx a = GToffoli [False] [a]

ccx :: br -> br -> br -> GToffoli br
ccx a b = GToffoli [True,True] [a,b]

cncx :: br -> br -> br -> GToffoli br
cncx a b = GToffoli [True,False] [a,b]

------------------------------------------------------------------------------
