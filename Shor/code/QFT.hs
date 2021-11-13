module QFT where

import Data.Complex

import Text.Printf

-------------------------------------------------------------------------------------
-- Roots of unity and their powers

type C = Complex Double

delta :: Double
delta = 1e-20

showC :: C -> String
showC (a :+ b) | abs b < delta = printf "%.20f" a
               | abs a < delta = printf "i(%.20f)" b
               | otherwise = printf "(%.20f) + i(%.20f)" a b

-- divide complex plane in 2^n turns

omegaN :: Int -> C
omegaN n = cis (2 * pi / (fromInteger (2 ^ n)))

-- divide complex plane in 2^n turns and go around 0,1,2,3,... times

omegaPowers :: Int -> [C]
omegaPowers n = [ wn ^ p | p <- [0..] ] where wn = omegaN n

-------------------------------------------------------------------------------------
-- Represent numbers in fourier basis

-- n = 4 bits; total number of rotations around complex plane = 16
-- units (# of rotations)  1/16 , 2/16 , 4/16 , 8/16
-- to represent x in fourier basis:
-- (w^1)^x, (w^2)^x, (w^4)^x, (w^8)^x

fourierBasis :: Int -> [C]
fourierBasis n = [ wn ^ (2 ^ i) | i <- [0..(n-1)] ] where wn = omegaN n

toFourierBasis :: Int -> Integer -> [C]
toFourierBasis n x = [ fb ^ x | fb <- fourierBasis n ] 
  
-------------------------------------------------------------------------------------
-- Now we need to do x, cx, and ccx in fourier basis

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------








{--
dft :: Int -> Int -> [C]
dft n k = [ w  ^ r | r <- [0..] ] where w = (omegaPowers n) !! k
  
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

-- zipWith (+) q0,q2,q4,q6

qs :: [[C]]
qs = map (take 16 . dft 16) [2,5,8,11,14,1]

rs :: [(Int,C)]
rs = [ (i,sum $ map (!! i) qs) | i <- [0..15]]

sq x = x * x

go :: IO ()
go = mapM_
  (\(i,c) ->
      putStrLn (printf "%2d => %.2f" i (sq (magnitude c))))
  rs

QFT_16 of |0> + |3> + |6> + |9>  + |12> + |15>
next to   |1> + |4> + |7> + |10 >+ |13> + |0> 
next to   |2> + |5> + |8> + |11 >+ |14> + |1> 

 0 => 36.00  36.00
 1 => 0.47    0.47
 2 => 0.59    0.59
 3 => 0.89    0.89
 4 => 2.00    2.00
 5 => 22.43  22.43
 6 => 3.41    3.41
 7 => 0.21    0.21
 8 => 0.00    0.00
 9 => 0.21    0.21
10 => 3.41    3.41
11 => 22.43  22.43
12 => 2.00    2.00
13 => 0.89    0.89
14 => 0.59    0.59
15 => 0.47    0.47

--}

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
