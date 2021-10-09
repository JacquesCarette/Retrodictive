module ShorPE where

import Data.Vector hiding (foldr, length, replicate, reverse, drop, take, splitAt, (++))
import qualified Data.Vector as V (replicate, drop, take, all, (++))
import Test.QuickCheck
import Numeric
import Control.Exception.Assert
import Debug.Trace

------------------------------------------------------------------------------
-- Mini reversible language for expmod

data W = W Int (Vector Bool)
  deriving (Eq,Show)

data Op = X Int
        | CX Int Int
        | CCX Int Int Int
        | COp Int Op
        | (:.:) Op Op
        | Alloc Int
        | DeAlloc Int

invert :: Op -> Op
invert (X i) = X i
invert (CX i j) = CX i j
invert (CCX i j k) = CCX i j k
invert (op1 :.: op2) = invert op2 :.: invert op1
invert (COp i op) = COp i (invert op)
invert (Alloc i) = DeAlloc i
invert (DeAlloc i) = Alloc i

neg :: Vector Bool -> Int -> Vector Bool
neg vec i = vec // [(i , not (vec ! i))]

interp :: Op -> W -> W
interp (X i) w@(W n vec) = -- trace ("X: " ++ show w ++ "\n") $
  W n (neg vec i)
interp (CX i j) w@(W n vec)
  | vec ! i = -- trace ("CX: " ++ show w ++ "\n") $
    W n (neg vec j)
  | otherwise = w
interp (CCX i j k) w@(W n vec)
  | vec ! i && vec ! j = -- trace ("CCX: " ++ show w ++ "\n") $
    W n (neg vec k)
  | otherwise = w
interp (COp i op) w@(W n vec)
  | vec ! i = -- trace ("COp: " ++ show w ++ "\n") $
    interp op w
  | otherwise = w
interp (op1 :.: op2) w = -- trace ("Seq: " ++ show w ++ "\n") $
  interp op2 (interp op1 w)
interp (Alloc i) w@(W n vec) = -- trace ("Alloc: " ++ show w ++ "\n") $
  W (n+i) (V.replicate i False V.++ vec)
interp (DeAlloc i) w@(W n vec) = -- trace ("DeAlloc: " ++ show w ++ "\n") $
  assert (V.all not (V.take i vec)) $   
  W (n-i) (V.drop i vec)

------------------------------------------------------------------------------
-- Follow Rieffel & Polak

-- sum c a b
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

-- addMod a b m
addModOp :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> Op
addModOp n (ai,ae) (bi,be) (mi,me) = 
  Alloc n :.: -- carry
  Alloc 1 :.: -- t
  addOp (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  invert (addOp (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1)) :.:
  CX (bi+n+1) 0 :.:
  COp 0 (addOp (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1)) :.:
  invert (addOp (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1)) :.:
  X (bi+n+1) :.:
  CX (bi+n+1) 0 :.:
  X (bi+n+1) :.:
  addOp (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  DeAlloc 1 :.:
  DeAlloc n
  
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
addGen = do n <- chooseInt (1, 20)
            let wn = 3 * n + 1
            let cs = replicate n False
            as <- vector n
            lowbs <- vector n
            let bs = False : lowbs
            return (W wn (fromList (cs ++ as ++ bs)))

addModGen :: Gen W
addModGen = do n <- chooseInt (2, 10)
               let wn = 3 * n + 1
               as <- vector n
               lowbsms <- suchThat (vector (2*n)) $ \bits ->
                            bools2nat (drop n bits) > max 1 (bools2nat (take n bits))
               return (W wn (fromList (as ++ (False : lowbsms))))

instance Arbitrary W where
--  arbitrary = addGen
  arbitrary = addModGen

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

addModProp :: W -> Bool
addModProp w@(W wn vec) =
  let n = (wn - 1) `div` 3
      actual = interp (addModOp n (0,n-1) (n,2*n) (2*n+1,3*n)) w
      (as,r) = splitAt n (toList vec)
      (bs,ms) = splitAt (n+1) r
      a = bools2nat as
      b = bools2nat bs
      m = bools2nat ms
      sum = if (a + b) >= m then (a + b) - m else (a + b)
      expected = W wn (fromList (as ++ nat2bools (n+1) sum ++ ms))
  in actual == expected 


------------------------------------------------------------------------------
