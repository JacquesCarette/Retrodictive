module ShorPE where

import Data.Vector hiding ((++))

------------------------------------------------------------------------------
-- Mini reversible language for expmod

type W = Vector Bool

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

neg :: Int -> W -> W
neg i w = w // [(i , not (w ! i))]

interp :: Op -> W -> W
interp (Swap i j) w = w // [(i , w ! j), (j , w ! i)]
interp (op1 :.: op2) w = interp op2 (interp op1 w)
interp (X i) w = neg i w
interp (CX i j) w | w ! i = neg j w
                  | otherwise = w
interp (CCX i j k) w | w ! i && w ! j = neg k w
                     | otherwise = w

------------------------------------------------------------------------------
-- Follow Rieffel & Polak

-- sum (c , a , b)
sumOp :: Int -> Int -> Int -> Op
sumOp c a b = CX a b :.:
              CX c b

-- carry c a b c'
carryOp :: Int -> Int -> Int -> Int -> Op
carryOp c a b c' = CCX a b c' :.:
                   CX a b :.:
                   CCX c b c' :.:
                   CX a b

-- add c a b
-- range includes beginning index; excludes ending index
addOp :: (Int,Int) -> (Int,Int) -> (Int,Int) -> Op
addOp (ci,ce) (ai,ae) (bi,be) | be - bi == 2 =
  carryOp ci ai (bi+1) bi :.:
  sumOp ci ai (bi+1)
                              | otherwise =
  carryOp (ce-1) (ae-1) (be-1) (ce-2) :.:
  addOp (ci,ce-1) (ai,ae-1) (bi,be-1) :.:
  invert (carryOp (ce-1) (ae-1) (be-1) (ce-2)) :.:
  sumOp (ce-1) (ae-1) (be-1)
  

------------------------------------------------------------------------------
v0 = fromList ([False,False,False] ++
               [False, True, False] ++ 
               [False, False, False, True])

t0 = interp (addOp (0,3) (4,7) (8,11)) v0

------------------------------------------------------------------------------
