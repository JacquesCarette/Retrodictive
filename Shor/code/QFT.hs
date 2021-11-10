module QFT where

import Data.Complex

import Text.Printf

-------------------------------------------------------------------------------------
-- A small experiment

-- Roots of unity and their powers

type C = Complex Double

omegaN :: Integer -> C
omegaN n = cis (2 * pi / (fromInteger n))

omegaNpowers :: Integer -> [C]
omegaNpowers n = [ wn ^ p | p <- [0..] ] where wn = omegaN n

dft :: Integer -> Int -> [C]
dft n k = [ w  ^ r | r <- [0..] ] where w = (omegaNpowers n) !! k
  
-- compute QFT_8 of |0> + |2> + |4> + |6>

q0 :: [C]
q0 = dft 8 0
-- q0 = [1,1,1,1,1,1,1,1]

q2 :: [C]
q2 = dft 8 2
-- q2 = [1,i,-1,-i,1,i,-1,-i]

q4 :: [C]
q4 = dft 8 4
-- q4 = [1,-1,1,-1,1,-1,1,-1]

q6 :: [C]
q6 = dft 8 6
-- q6 = [1,-i,-1,i,1,-i,-1,i]


-------------------------------------------------------------------------------------

-- Do classical simulation of QFT

-- Shor:

-- Stage I and measure: easy to simulate classically; just pick a random number

-- Stage I and II and measure: easy to simulate classically; just pick
-- a random number and apply expmod

-- Stage III and measure: can be done classically apparently

-- Some simple state II (let's call it II') and then III: can
-- apparently also be done classically

-- So what gives? 

-- Sec. 7.4.2 of book shows that Grover has the same pattern; might be able to do
-- something with it

-- if we get rid of ccx, becomes 2SAT or some decidable graph
-- algorithm or some variant of Ising model that is decidable

-------------------------------------------------------------------------------------
