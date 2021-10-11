{-# LANGUAGE TemplateHaskell #-}

module ShorPE where

import Data.Char
import Data.Vector (Vector, fromList, toList, (!), (//))
import qualified Data.Vector as V 

import Text.Printf
import Test.QuickCheck
import Control.Exception.Assert

-- import Debug.Trace

trace :: String -> a -> a
trace s a = a

------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Syntax

data OP = CX Int Int                       -- if first true; negate second
        | NCX Int Int                      -- if first false; negate second
        | CCX Int Int Int                  -- if first,second true; negate third
        | COP Int OP                       -- if first true; apply op
        | NCOP Int OP                      -- if first false; apply op
        | SWAP Int Int                     -- swap values at given indices
        | (:.:) OP OP                      -- sequential composition
        | ALLOC Int                        -- alloc n bits to front
        | DEALLOC Int                      -- dealloc n bits from front
        | LOOP [Int] (Int -> OP)           -- apply fun to each of indices
        | ASSERT String String (W -> Bool) -- no op; used for debugging

instance Show OP where
  show op = showH "" op
    where
      showH d (CX i j)        = printf "%sCX %d %d" d i j
      showH d (NCX i j)       = printf "%sNCX %d %d" d i j
      showH d (CCX i j k)     = printf "%sCCX %d %d %d" d i j k
      showH d (COP i op)      = printf "%sCOP %d (\n%s)" d i (showH ("  " ++ d) op)
      showH d (NCOP i op)     = printf "%sNCOP %d (\n%s)" d i (showH ("  " ++ d) op)
      showH d (SWAP i j)      = printf "%sSWAP %d %d" d i j
      showH d (op1 :.: op2)   = printf "%s :.:\n%s" (showH d op1) (showH d op2)
      showH d (ALLOC i)       = printf "%sALLOC %d" d i
      showH d (DEALLOC i)     = printf "%sDEALLOC %d" d i
      showH d (LOOP [] f)     = printf ""
      showH d (LOOP [i] f)    = printf "%s" (showH d (f i))
      showH d (LOOP (i:is) f) = printf "%s\n%s" (showH d (f i)) (showH d (LOOP is f))
      showH d (ASSERT s s' f) = printf ""

invert :: OP -> OP
invert (CX i j)         = CX i j
invert (NCX i j)        = NCX i j
invert (CCX i j k)      = CCX i j k
invert (COP i op)       = COP i (invert op)
invert (NCOP i op)      = NCOP i (invert op)
invert (SWAP i j)       = SWAP i j
invert (op1 :.: op2)    = invert op2 :.: invert op1
invert (ALLOC i)        = DEALLOC i
invert (DEALLOC i)      = ALLOC i
invert (LOOP indices f) = LOOP (reverse indices) (\k -> invert (f k))
invert (ASSERT s s' f)  = ASSERT s s' f
       
------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Runtime state is a vector of booleans

-- W size vector-of-bits

data W = W Int (Vector Bool)
  deriving Eq

instance Show W where
  show (W n vec) =
    printf "\t[%d] %s" n (concat (V.map (show . fromEnum) vec))

list2W :: [Bool] -> W
list2W bits = W (length bits) (fromList bits)

string2W :: String -> W
string2W bits = list2W (map (toEnum . digitToInt) bits)

toInt :: Vector Bool -> Int
toInt bs = V.foldr (\b n -> fromEnum b + 2*n) 0 (V.reverse bs)

fromInt :: Int -> Int -> Vector Bool
fromInt len n = V.replicate (len - length bits) False V.++ fromList bits
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum r : bin q
        bits = reverse (bin n)

notI :: Vector Bool -> Int -> Vector Bool
notI vec i = vec // [(i , not (vec ! i))]

------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Interpreter

interp :: OP -> W -> W
interp op w@(W n vec) = 
  case op of                         

    CX i j | vec ! i ->
      assert (j < n) $
      trace (printf "%s\n%s" (show w) (show op)) $
      W n (notI vec j)
    CX _ _ -> w

    NCX i j | not (vec ! i) ->
      assert (j < n) $ 
      trace (printf "%s\n%s" (show w) (show op)) $
      W n (notI vec j)
    NCX _ _ -> w

    CCX i j k | vec ! i && vec ! j -> 
      assert (k < n) $ 
      trace (printf "%s\n%s" (show w) (show op)) $
      W n (notI vec k)
    CCX _ _ _ -> w

    COP i op | vec ! i ->
      interp op w
    COP _ _ -> w

    NCOP i op | not (vec ! i) ->
      interp op w
    NCOP _ _ -> w

    SWAP i j ->
      assert (i < n && j < n) $ 
      trace (printf "%s\n%s" (show w) (show op)) $
      W n (vec // [ (i , vec ! j), (j , (vec ! i)) ])

    op1 :.: op2 -> 
      interp op2 (interp op1 w)

    ALLOC i -> 
      trace (printf "%s\n%s" (show w) (show op)) $
      W (n+i) (V.replicate i False V.++ vec)

    DEALLOC i ->
      assert (n > i) $
      trace (printf "%s\n%s" (show w) (show op)) $
      W (n-i) (V.drop i vec)

    LOOP indices f -> 
      loop indices w
        where loop [] w = w
              loop (i:is) w = loop is (interp (f i) w)

    ASSERT s s' f ->
      assertMessage s s' (assert (f w)) w

------------------------------------------------------------------------------
-- Circuits following Ch.6 of:
-- Quantum Computing: A Gentle Introduction by Rieffel & Polak

-- Simple helpers

-- sum: c, a, b => c, a, (a+b+c) mod 2

sumOP :: Int -> Int -> Int -> OP
sumOP c a b =
  CX a b :.:
  CX c b

t0 = interp (sumOP 0 1 2) (string2W "000") -- 000
t1 = interp (sumOP 0 1 2) (string2W "001") -- 001
t2 = interp (sumOP 0 1 2) (string2W "010") -- 011
t3 = interp (sumOP 0 1 2) (string2W "011") -- 010
t4 = interp (sumOP 0 1 2) (string2W "100") -- 101
t5 = interp (sumOP 0 1 2) (string2W "101") -- 100
t6 = interp (sumOP 0 1 2) (string2W "110") -- 110
t7 = interp (sumOP 0 1 2) (string2W "111") -- 111

prop_sum :: Bool
prop_sum =
  assert (t0 == string2W "000") $
  assert (t1 == string2W "001") $
  assert (t2 == string2W "011") $
  assert (t3 == string2W "010") $
  assert (t4 == string2W "101") $
  assert (t5 == string2W "100") $
  assert (t6 == string2W "110") $
  assert (t7 == string2W "111") $
  True

-- carry: c, a, b, c' => c, a, b, c' xor F(a,b,c)
-- where F(a,b,c) = 1 if two or more inputs are 1

carryOP :: Int -> Int -> Int -> Int -> OP
carryOP c a b c' =
  CCX a b c' :.:
  CX a b :.:
  CCX c b c' :.:
  CX a b

t08 = interp (carryOP 0 1 2 3) (string2W "0000") -- 0000
t09 = interp (carryOP 0 1 2 3) (string2W "0001") -- 0001
t10 = interp (carryOP 0 1 2 3) (string2W "0010") -- 0010
t11 = interp (carryOP 0 1 2 3) (string2W "0011") -- 0011
t12 = interp (carryOP 0 1 2 3) (string2W "0100") -- 0100
t13 = interp (carryOP 0 1 2 3) (string2W "0101") -- 0101
t14 = interp (carryOP 0 1 2 3) (string2W "0110") -- 0111
t15 = interp (carryOP 0 1 2 3) (string2W "0111") -- 0110
t16 = interp (carryOP 0 1 2 3) (string2W "1000") -- 1000
t17 = interp (carryOP 0 1 2 3) (string2W "1001") -- 1001
t18 = interp (carryOP 0 1 2 3) (string2W "1010") -- 1011
t19 = interp (carryOP 0 1 2 3) (string2W "1011") -- 1010
t20 = interp (carryOP 0 1 2 3) (string2W "1100") -- 1101
t21 = interp (carryOP 0 1 2 3) (string2W "1101") -- 1100
t22 = interp (carryOP 0 1 2 3) (string2W "1110") -- 1111
t23 = interp (carryOP 0 1 2 3) (string2W "1111") -- 1110

prop_carry :: Bool
prop_carry =
  assert (t08 == string2W "0000") $
  assert (t09 == string2W "0001") $
  assert (t10 == string2W "0010") $
  assert (t11 == string2W "0011") $
  assert (t12 == string2W "0100") $
  assert (t13 == string2W "0101") $
  assert (t14 == string2W "0111") $
  assert (t15 == string2W "0110") $
  assert (t16 == string2W "1000") $
  assert (t17 == string2W "1001") $
  assert (t18 == string2W "1011") $
  assert (t19 == string2W "1010") $
  assert (t20 == string2W "1101") $
  assert (t21 == string2W "1100") $
  assert (t22 == string2W "1111") $
  assert (t23 == string2W "1110") $
  True

-- takes n-bits [a, b, c, ... , y, z] stored in the range (i,e)
-- and produces [b, c, ... , y, z, a]
--
-- when a=0, this is multiplication by 2

shiftOP :: (Int,Int) -> OP
shiftOP (i,e) =
  LOOP [i..(e-1)] (\k -> SWAP k (k+1))

shiftOPGuard :: (Int,Int) -> OP
shiftOPGuard (i,e) =
  ASSERT "shiftOP" "Precondition wn >= n failed"
    (\w@(W wn vec) -> wn >= e-i+1) :.:
  ASSERT "shiftOP" "Precondition x[n] == 0 failed"
    (\w@(W wn vec) -> vec ! i == False) :.:
  shiftOP (i,e)

prop_shift :: Property
prop_shift = forAll
  (do n <- chooseInt (1,40)
      xs <- vector n
      return (W (n+1) (fromList (False : xs))))
  (\ w@(W wn vec) ->
    let actual = interp (shiftOPGuard (0,wn-1)) w
        res = 2 * toInt vec
        expected = W wn (fromInt wn res)
    in actual === expected)

-- a has n-bits stored in the range (ai,ae)
-- b has n-bits stored in the range (bi,be)
--   initialized to 0

-- copy: a , 0 => a, a

copyOP :: Int -> (Int,Int) -> (Int,Int) -> OP
copyOP n (ai,ae) (bi,be) =
  LOOP [0..(n-1)] (\k -> CX (ai+k) (bi+k))

copyOPGuard :: Int -> (Int,Int) -> (Int,Int) -> OP
copyOPGuard n (ai,ae) (bi,be) =
  ASSERT "copyOP" "Precondition wn >= 2n failed"
    (\w@(W wn vec) -> wn >= 2*n) :.:
  ASSERT "copyOP" "Precondition b == 0 failed"
    (\w@(W wn vec) -> toInt (V.slice n n vec) == 0) :.:
  copyOP n (ai,ae) (bi,be)

prop_copy :: Property
prop_copy = forAll
  (do n <- chooseInt (1,40)
      as <- vector n
      let bs = replicate n False
      return (W (2*n) (fromList (as ++ bs))))
  (\ w@(W wn vec) ->
    let n = wn `div` 2
        actual = interp (copyOPGuard n (0,n-1) (n,2*n-1)) w
        as = V.take n vec
        expected = W wn (as V.++ as)
    in actual === expected)

------------------------------------------------------------------------------
-- Addition of n-bit numbers

-- c has n-bits stored in the range (ci,ce) inclusive
--   initialized to 0
-- a has n bits stored in the range (ai,ae)
-- b has (n+1)-bits stored in the range (bi,be)

-- add:  0, a, b => 0, a, (a + b) `mod` (2 ^ (n+1))
-- sub:  0, a, b => 0, a, (b - a) (+ 2 ^ (n+1) if (b-a) negative)

addOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
addOP n (ci,ce) (ai,ae) (bi,be)
  | n == 1 =
    carryOP ci ai be bi :.:
    sumOP ci ai be
  | otherwise =
    carryOP ce ae be (ce-1) :.:
    addOP (n-1) (ci,ce-1) (ai,ae-1) (bi,be-1) :.:
    invert (carryOP ce ae be (ce-1)) :.:
    sumOP ce ae be

-- Assertions and testing

addOPGuard :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
addOPGuard n (ci,ce) (ai,ae) (bi,be) =
  assert ((ce-ci) == (n-1) && (ae-ai) == (n-1) && (be-bi) == n) $ 
  ASSERT "addOP" "Precondition wn >= 3n+1 failed"
    (\ (W wn _) -> wn >= 3*n + 1) :.:
  ASSERT "addOP" "Precondition c == 0 failed'"
    (\ (W _ vec) -> toInt (V.slice ci n vec) == 0) :.:
  addOP n (ci,ce) (ai,ae) (bi,be) :.:
  ASSERT "addOP" "Postcondition c == 0 failed"
    (\ (W _ vec) -> toInt (V.slice ci n vec) == 0)

subOPGuard :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
subOPGuard n (ci,ce) (ai,ae) (bi,be) =
  assert ((ce-ci) == (n-1) && (ae-ai) == (n-1) && (be-bi) == n) $ 
  ASSERT "subOP" "Precondition wn >= 3n+1 failed"
    (\ (W wn _) -> wn >= 3*n + 1) :.:
  ASSERT "subOP" "Precondition c == 0 failed'"
    (\ (W _ vec) -> toInt (V.slice ci n vec) == 0) :.:
  invert (addOP n (ci,ce) (ai,ae) (bi,be)) :.:
  ASSERT "subOP" "Postcondition c == 0 failed"
    (\ (W _ vec) -> toInt (V.slice ci n vec) == 0)

addGen :: Gen W
addGen =
  do n <- chooseInt (1, 40)
     let wn = 3 * n + 1
     let cs = replicate n False
     as <- vector n
     bs <- vector (n+1)
     return (W wn (fromList (cs ++ as ++ bs)))

prop_add :: Property
prop_add = forAll addGen $ \ w@(W wn vec) ->
  let n = (wn - 1) `div` 3
      actual = interp (addOPGuard n (0,n-1) (n,2*n-1) (2*n,3*n)) w
      (cs,r) = V.splitAt n vec
      (as,bs) = V.splitAt n r
      sum = (toInt as + toInt bs) `mod` (2 ^ (n+1))
      sums = fromInt (n+1) sum
      expected = W wn (cs V.++ as V.++ sums)
  in actual === expected

prop_sub :: Property
prop_sub = forAll addGen $ \ w@(W wn vec) ->
  let n = (wn - 1) `div` 3
      actual = interp (subOPGuard n (0,n-1) (n,2*n-1) (2*n,3*n)) w
      (cs,r) = V.splitAt n vec
      (as,bs) = V.splitAt n r
      diff = toInt bs - toInt as
      diffs = fromInt (n+1) (if diff < 0 then diff + 2 ^ (n+1) else diff)
      expected = W wn (cs V.++ as V.++ diffs)
  in actual === expected

------------------------------------------------------------------------------
-- Addition of n-bit numbers modulo another n-bit number

-- a has n-bits stored in the range (ai,ae)
-- b has (n+1)-bits stored in the range (bi,be)
-- m has n-bits stored in the range (mi,me)
-- precondition: a < m and b < m and m > 0 to make sense of mod

-- addMod: a, b, m => a, (a+b) `mod` m, m
-- subMod: a, b, m => a, (b-a)*, m where we add m to (b-a) if negative

addModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
addModOP n (ai,ae) (bi,be) (mi,me) = 
  ALLOC n :.: -- carry
  ALLOC 1 :.: -- t
  addOPGuard n (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  subOPGuard n (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1) :.:
  CX (bi+n+1) 0 :.:
  COP 0 (addOPGuard n (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1)) :.:
  subOPGuard n (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  NCX (bi+n+1) 0 :.:
  addOPGuard n (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  ASSERT "addModOP" "Failed to restore t to 0"
    (\ (W _ vec) -> vec ! 0 == False) :.:
  DEALLOC 1 :.:
  ASSERT "addModOP" "Failed to restore carry to 0"
    (\ (W _ vec) -> toInt (V.slice 0 n vec) == 0) :.:
  DEALLOC n

-- Assertions and testing

addModOPGuard :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
addModOPGuard n (ai,ae) (bi,be) (mi,me) = 
  assert ((ae-ai) == (n-1) && (be-bi) == n && (me-mi) == (n-1)) $ 
  ASSERT "addModOP" "Precondition wn >= 3n+1 failed"
    (\ (W wn _) -> wn >= 3*n + 1) :.:
  ASSERT "addModOP" "Precondition a < m failed'"
    (\ (W _ vec) -> toInt (V.slice ai n vec) < toInt (V.slice mi n vec)) :.:
  ASSERT "addModOP" "Precondition b < m failed'"
    (\ (W _ vec) -> toInt (V.slice bi n vec) < toInt (V.slice mi n vec)) :.:
  addModOP n (ai,ae) (bi,be) (mi,me) 

subModOPGuard :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
subModOPGuard n (ai,ae) (bi,be) (mi,me) = 
  assert ((ae-ai) == (n-1) && (be-bi) == n && (me-mi) == (n-1)) $ 
  ASSERT "subModOP" "Precondition wn >= 3n+1 failed"
    (\ (W wn _) -> wn >= 3*n + 1) :.:
  ASSERT "subModOP" "Precondition a < m failed'"
    (\ (W _ vec) -> toInt (V.slice ai n vec) < toInt (V.slice mi n vec)) :.:
  ASSERT "subModOP" "Precondition b < m failed'"
    (\ (W _ vec) -> toInt (V.slice bi n vec) < toInt (V.slice mi n vec)) :.:
  invert (addModOP n (ai,ae) (bi,be) (mi,me))

addModGen :: Gen W
addModGen =
  do n <- chooseInt (1, 40)
     let wn = 3 * n + 1
     m <- chooseInt (1, 2^n-1)
     a <- chooseInt (0,m-1)
     b <- chooseInt (0,m-1)
     return (W wn (fromInt n a V.++ fromInt (n+1) b V.++ fromInt n m))

prop_addMod :: Property
prop_addMod = forAll addModGen $ \ w@(W wn vec) ->
  let n = (wn - 1) `div` 3
      actual = interp (addModOPGuard n (0,n-1) (n,2*n) (2*n+1,3*n)) w
      (as,r) = V.splitAt n vec
      (bs,ms) = V.splitAt (n+1) r
      a = toInt as
      b = toInt bs
      m = toInt ms
      sum = (a + b) `mod` m
      expected = W wn (as V.++ fromInt (n+1) sum V.++ ms)
  in actual === expected

prop_subMod :: Property
prop_subMod = forAll addModGen $ \ w@(W wn vec) ->
  let n = (wn - 1) `div` 3
      actual = interp (subModOPGuard n (0,n-1) (n,2*n) (2*n+1,3*n)) w
      (as,r) = V.splitAt n vec
      (bs,ms) = V.splitAt (n+1) r
      a = toInt as
      b = toInt bs
      m = toInt ms
      diff = b - a
      diffs = fromInt (n+1) (if diff < 0 then diff + m else diff)
      expected = W wn (as V.++ diffs V.++ ms)
  in actual === expected

------------------------------------------------------------------------------
-- 

{--
-- timesMod a b m p
timesModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
timesModOP n (ai,ae) (bi,be) (mi,me) (pi,pe) =
  ALLOC n :.: -- carry
  ALLOC n :.: -- t
  LOOP [0..(n-1)] (\i ->
    invert (addOPGuard n (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n)) :.:
    CX (ai+2*n) i :.:
    COP i (addOPGuard n (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n)) :.: 
    COP (be+2*n-i) (addModOPGuard n (ai+2*n+1,ae+2*n) (pi+2*n,pe+2*n) (mi+2*n,me+2*n)) :.: 
    shiftOPGuard (ai+2*n,ae+2*n) 
  ) :.:
  LOOP [(n-1),(n-2)..0] (\i ->
    invert (shiftOPGuard (ai+2*n,ae+2*n)) :.:
    COP i (invert (addOPGuard n (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n))) :.: 
    CX (ai+2*n) i :.:
    addOPGuard n (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n)
  ) :.:
  DEALLOC n :.:
  DEALLOC n

-- squareMod a m s
squareModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
squareModOP n (ai,ae) (mi,me) (si,se) =
  ALLOC n :.: -- t
  copyOPGuard n (ai+n+1,ae+n) (0,n-1) :.:
  timesModOP n (ai+n,ae+n) (0,n-1) (mi+n,me+n) (si+n,se+n) :.:
  invert (copyOPGuard n (ai+n+1,ae+n) (0,n-1)) :.:
  DEALLOC n

-- expMod a b m p e
expModOP :: Int -> Int ->
            (Int,Int) -> (Int,Int) -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
expModOP n k (ai,ae) (bi,be) (mi,me) (pi,pe) (ei,ee)
  | k == 1 =
    NCOP bi (copyOPGuard (n+1) (pi,pe) (ei,ee)) :.:
    COP bi (timesModOP n (ai,ae) (pi,pe) (mi,me) (ei,ee)) 
  | otherwise =
    ALLOC (n+1) :.: -- v
    ALLOC (n+1) :.: -- u
    NCOP (be+d) (copyOPGuard (n+1) (pi+d,pe+d) (n+1,2*n+1)) :.:
    COP (be+d) (timesModOP n (ai+d,ae+d) (pi+d,pe+d) (mi+d,me+d) (ei+d,ee+d)) :.:
    squareModOP n (ai+d,ae+d) (mi+d,me+d) (0,n) :.:
    expModOP n (k-1) (0,n) (bi+d,be+d-1) (mi+d,me+d) (n+1,2*n+1) (ei+d,ee+d) :.:
    invert (squareModOP n (ai+d,ae+d) (mi+d,me+d) (0,n)) :.:
    COP (be+d) (invert (timesModOP n (ai+d,ae+d) (pi+d,pe+d) (mi+d,me+d) (ei+d,ee+d))) :.:
    NCOP (be+d) (invert (copyOPGuard (n+1) (pi+d,pe+d) (n+1,2*n+1))) :.:
    DEALLOC (n+1) :.: 
    DEALLOC (n+1) 
    where d = 2*n + 2

------------------------------------------------------------------------------
-- Testing

timesModGen :: Gen W
timesModGen = do n <- chooseInt (2, 20)
                 let wn = 4 * n + 2
                 lowasbsms <- suchThat (vector (3*n)) $ \bits ->
                                toInt (take n bits) < toInt (drop (2*n) bits)
                 let ps = replicate n False 
                 return (W wn (fromList ((False : lowasbsms) ++ (False : ps))))

expModGen :: Gen W
expModGen = do n <- chooseInt (2, 20)
               let wn = 5 * n + 3
               lowas <- suchThat (vector n) $ \bits -> toInt bits > 0
               let as = False : lowas
               bs <- vector n
               ms <- suchThat (vector n) $ \bits -> toInt bits > 1
               let ps = (replicate n False) ++ [True]
               let es = replicate (n+1) False
               return (W wn (fromList (as ++ bs ++ ms ++ ps ++ es)))

timesModProp :: W -> Bool
timesModProp w@(W wn vec) =
  let n = (wn - 2) `div` 4
      actual = interp (timesModOP n (0,n) (n+1,2*n) (2*n+1,3*n) (3*n+1,4*n+1)) w
      (as,r) = splitAt (n+1) (toList vec)
      (bs,r') = splitAt n r
      (ms,ps) = splitAt n r'
      a = toInt as
      b = toInt bs
      m = toInt ms
      p = toInt ps
      res = (p + b * a) `mod` m
      expected = W wn (fromList (as ++ bs ++ ms ++ fromInt (n+1) res))
  in actual == expected 

expModProp :: W -> Bool
expModProp w@(W wn vec) =
  let n = (wn - 3) `div` 5
      actual = interp
                 (expModOP n n
                  (0,n) (n+1,2*n) (2*n+1,3*n) (3*n+1,4*n+1) (4*n+2,5*n+2))
               w
      (as,r) = splitAt (n+1) (toList vec)
      (bs,r') = splitAt n r
      (ms,r'') = splitAt n r'
      (ps,_) = splitAt (n+1) r''
      a = toInt as
      b = toInt bs
      m = toInt ms
      p = toInt ps
      res = (a ^ b) `mod` m
      expected = W wn (fromList (as ++ bs ++ ms ++ ps ++ fromInt (n+1) res))
  in actual == expected 

------------------------------------------------------------------------------
--}

-------------------------------------------------------------------------------
-- Run all tests

return [] -- Weird TH hack !!!
checks = $quickCheckAll

------------------------------------------------------------------------------

