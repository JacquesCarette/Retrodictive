module QFT where

import Data.Complex
import Data.List

import Text.Printf

--

import Numeric (doublemods)

{--


What is the Fourier transform of a formula

  ands0 + ands1 + ands2 + ...


Try simple things:

FT_4 (x0 + x1) = 9

if we expand x0=0,x1=1 or x0=1,x1=0

0001  1, 2, 4, 8
0010  2, 4, 8, 0
0101  5,10, 4, 8
0110  6,12, 8, 0
1001  9, 2, 4, 8
1010 10, 4, 8, 0
1101 13,10, 4, 8
1110 15,14,12, 8
----------------
     13,10, 4, 8 ==> 9


FT_4 (x0 x1) = 4

if we expand x0=1,x1=1 

0011  3, 6,12, 8
0111  7,14,12, 8
1011 11, 6,12, 8
1111 15,14,12, 8
----------------
      4, 8, 0, 0 ==> 4



No need to forget about boolean value or ALL variables
Try to keep track of values; if they get too complex then run with approximation

n = 4
period = 3

0000
0011
0110
1001
1100
1111
0010
0101
1000
1011
1110
0001
0100
0111
1010
1101
0000

All the numbers are really involved in the cycle

--}

-------------------------------------------------------------------------------------
-- Roots of unity 

type C = Complex Double

-- divide complex plane in 2^n turns; each turn is (omegaN n)

omegaN :: Int -> C
omegaN n = cis (2 * pi / (fromInteger (2 ^ n)))

-- Some simple control over howing complex numbers

-- when a number is close enough to 0

delta :: Double
delta = 1e-20

-- format strings

digits :: Int -> String
digits = printf "%%.%df" 

digitsPar :: Int -> String
digitsPar deltaP = "(" ++ digits deltaP ++ ")"

showC :: Int -> C -> String
showC deltaP (a :+ b)
  | abs b < delta = printf (digits deltaP) a
  | abs a < delta = printf ("i" ++ digitsPar deltaP) b
  | otherwise = printf (digitsPar deltaP ++ " + i" ++ digitsPar deltaP) a b 

printC :: Int -> [C] -> IO ()
printC deltaP = mapM_ (putStrLn . showC deltaP)

-------------------------------------------------------------------------------------
-- Represent numbers in fourier basis

-- Things are reasonably accurate until dimension n ~ 500

-- Fourier basis

-- when n=2, the complex plane is divided in four regions and the unit
-- of rotation is pi/2;
-- the representation of a number x in this Fourier basis is [x, 2x]
-- where each entry represents the number of turns to perform. So

-- 0 |-> [0,0]         so [ right , right ]
-- 1 |-> [1,2]         so [ up , left ]
-- 2 |-> [2,4] = [2,0] so [ left, right ]
-- 3 |-> [3,6] = [3,2] so [ down , left ]

-- gives the numbers of rotations to perform in each position

toFourierBasis :: Int -> Integer -> [Integer]
toFourierBasis n x = take n (doublemods (x `mod` 2 ^ n)(2 ^ n))

-- > map (toFourierBasis 2) [0..3]
-- [[0,0],[1,2],[2,0],[3,2]]

-- actually do the rotations

valueFB :: Int -> [Integer] -> [C]
valueFB n = map ((omegaN n) ^)

-- > map (valueFB 2 . toFourierBasis 2) [0..3]
-- [ 1, 1]
-- [ i,-1]
-- [-1, 1]
-- [-i,-1]

-- We are more interested in the opposite direction

-- If we know one coefficient and its index, what can we say
-- about the corresponding number in the computational basis
-- In the example:

-- 0 |-> [0,0] |-> [ 1, 1]
-- 1 |-> [1,2] |-> [ i,-1]
-- 2 |-> [2,0] |-> [-1, 1]
-- 3 |-> [3,2] |-> [-i,-1]

-- say we know that second position (pos) is 1
-- we calculate that the exponent (expon) must be 0
-- and then we solve for x:
--        x (2 ^ pos) = expon mod (2 ^ n)
-- i.e.   2x = 0 mod 4
-- to get x = [0,2]

fromFourierBasis :: Int -> (Int,C) -> [Integer]
fromFourierBasis n (fi,fc) = sort . nub $ xs
  where expon = round $ realPart $ log fc / log (omegaN n)
        xs = [ ((2^n * y + expon) `div` (2 ^ fi)) `mod` (2 ^ n)
             | y <- [0..((2 ^ n) - 1)]]
  
-- In Shor's algorithm, we measure one number in the Fourier
-- basis. Let n = 8, N = 2^n = 256, and say we measured:
-- [123,246,236,216,176,96,192,128]
-- which is 123 in that FourierBasis.
-- We are promised this number is close to 2^n / period

-- When evaluating backwards, we don't know this number but we know
-- that what was measured was of the form:
-- 
-- [    q `mod` N
-- ,   2q `mod` N
-- ,   4q `mod` N
-- ,   8q `mod` N
-- ,  16q `mod` N
-- ,  32q `mod` N
-- ,  64q `mod` N
-- , 128q `mod` N
-- ]
--
-- for some unknown q

-- Let's feed this through QFT backwards to see what we get in terms
-- in the computational basis in terms of the unkonwn q



-------------------------------------------------------------------------------------
-- test

testFB :: Int -> Integer -> Int -> [Integer]
testFB n x pos = fromFourierBasis n (pos,cs !! pos)
  where cs = valueFB n $ toFourierBasis n x

-- When pos = 0, we recover the number exactly
-- QFT> map (\y -> testFB 2 y 0) [0..3]
-- [[0],[1],[2],[3]]

-- When pos = 1, we recover numbers with the same parity
-- QFT> map (\y -> testFB 2 y 1) [0..3]
-- [[0,2],[1,3],[0,2],[1,3]]

-------------------------------------------------------------------------------------
-- Now we need to do x, cx, and ccx in fourier basis

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------








{--

omegaPowers :: Int -> [C]
omegaPowers n = [ wn ^ p | p <- [0..] ] where wn = omegaN n

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

--}

