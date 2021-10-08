{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module ShorPE where

import Data.Vector hiding (foldr, length, replicate, reverse, splitAt, (++))
import Test.QuickCheck
import Numeric
import Control.Exception.Assert

------------------------------------------------------------------------------
-- Mini reversible language for expmod

data W = W Int (Vector Bool)
  deriving (Eq,Show)

data Op = Swap Int Int 
        | (:.:) Op Op
        | X Int
        | CX Int Int
        | CCX Int Int Int

invert :: Op -> Op
invert (Swap i j) = Swap i j
invert (op1 :.: op2) = invert op2 :.: invert op1
invert (X i) = X i
invert (CX i j) = CX i j
invert (CCX i j k) = CCX i j k

neg :: Vector Bool -> Int -> Vector Bool
neg vec i = vec // [(i , not (vec ! i))]

interp :: Op -> W -> W
interp (Swap i j) (W n vec) = W n (vec // [(i , vec ! j), (j , vec ! i)])
interp (op1 :.: op2) w = interp op2 (interp op1 w)
interp (X i) (W n vec) = W n (neg vec i)
interp (CX i j) w@(W n vec)
  | vec ! i = W n (neg vec j)
  | otherwise = w
interp (CCX i j k) w@(W n vec)
  | vec ! i && vec ! j = W n (neg vec k)
  | otherwise = w

------------------------------------------------------------------------------
-- Follow Rieffel & Polak

-- sum (c , a , b)
sumOp :: Int -> Int -> Int -> Op
sumOp c a b =
  CX a b :.:
  CX c b

-- carry c a b c'
carryOp :: Int -> Int -> Int -> Int -> Op
carryOp c a b c' =
  CCX a b c' :.:
  CX a b :.:
  CCX c b c' :.:
  CX a b

-- add c a b
-- range inclusive
addOp :: (Int,Int) -> (Int,Int) -> (Int,Int) -> Op
addOp (ci,ce) (ai,ae) (bi,be)
  | be - bi == 1 =
    assert (ci == ce && ai == ae) $ 
    carryOp ci ai (bi+1) bi :.:
    sumOp ci ai (bi+1)
  | otherwise =
    carryOp ce ae be (ce-1) :.:
    addOp (ci,ce-1) (ai,ae-1) (bi,be-1) :.:
    invert (carryOp ce ae be (ce-1)) :.:
    sumOp ce ae be
  
------------------------------------------------------------------------------
-- Testing

bit :: Int -> Bool
bit 0 = False
bit 1 = True

nat2bools :: Int -> Int -> [Bool]
nat2bools len n = replicate (len - length bits) False ++ bits
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in bit r : bin q
        bits = reverse (bin n)
  
bools2nat :: [Bool] -> Int
bools2nat bs = foldr (\b n -> fromEnum b + 2*n) 0 (reverse bs)

addGen :: Gen W
addGen = do n <- chooseInt (1, 2)
            let wn = 3 * n + 1
            bools <- vector wn
            return (W wn (fromList bools))

instance Arbitrary W where
  arbitrary = addGen

addProp :: W -> Bool
addProp w@(W wn vec) =
  let n = (wn - 1) `div` 3
      actual = interp (addOp (0,n-1) (n,2*n-1) (2*n,3*n)) w
      (cs,r) = splitAt n (toList vec)
      (as,bs) = splitAt n r
      a = bools2nat as
      b = bools2nat bs
      c = bools2nat cs
      sum = (a + b + c) `mod` (2 ^ (n + 1))
      expected = W wn (fromList (cs ++ as ++ nat2bools (n+1) sum))
  in actual == expected 

------------------------------------------------------------------------------
