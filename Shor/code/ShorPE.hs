module ShorPE where

import Data.Vector (Vector, fromList, toList, (!), (//))
import qualified Data.Vector as V 

import Debug.Trace
import Text.Printf
import Test.QuickCheck
import Control.Exception.Assert

------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Syntax

data OP = CX Int Int                    -- if first true; negate second
        | NCX Int Int                   -- if first false; negate second
        | CCX Int Int Int               -- if first,second true; negate third
        | COP Int OP                    -- if first true; apply op
        | NCOP Int OP                   -- if first false; apply op
        | SWAP Int Int                  -- swap values at given indices
        | (:.:) OP OP                   -- sequential composition
        | ALLOC Int                     -- alloc n bits to front
        | DEALLOC Int                   -- dealloc n bits from front
        | LOOP [Int] (Int -> OP)        -- apply fun to each of indices

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
       
------------------------------------------------------------------------------
-- Mini reversible language for expmod circuits
-- Interpreter: state is maintained as a vector of booleaans

-- W size bits
data W = W Int (Vector Bool)
  deriving Eq

instance Show W where
  show (W n vec) =
    printf "\t[%d] %s" n (concat (V.map (show . fromEnum) vec))

notI :: Vector Bool -> Int -> Vector Bool
notI vec i = vec // [(i , not (vec ! i))]

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
      trace (printf "%s\n%s" (show w) (show op)) $
      W (n-i) (V.drop i vec)

    LOOP indices f -> 
      loop indices w
        where loop [] w = w
              loop (i:is) w = loop is (interp (f i) w)


------------------------------------------------------------------------------
-- Circuits following Rieffel & Polak

-- sum c a b
sumOP :: Int -> Int -> Int -> OP
sumOP c a b =
  CX a b :.:
  CX c b

-- carry c a b c'
carryOP :: Int -> Int -> Int -> Int -> OP
carryOP c a b c' =
  CCX a b c' :.:
  CX a b :.:
  CCX c b c' :.:
  CX a b

-- add c a b
addOP :: (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
addOP (ci,ce) (ai,ae) (bi,be)
  | be - bi == 1 =
    assert (ci == ce && ai == ae) $ 
    carryOP ci ai (bi+1) bi :.:
    sumOP ci ai (bi+1)
  | otherwise =
    carryOP ce ae be (ce-1) :.:
    addOP (ci,ce-1) (ai,ae-1) (bi,be-1) :.:
    invert (carryOP ce ae be (ce-1)) :.:
    sumOP ce ae be

-- addMod a b m
addModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
addModOP n (ai,ae) (bi,be) (mi,me) = 
  ALLOC n :.: -- carry
  ALLOC 1 :.: -- t
  addOP (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  invert (addOP (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1)) :.:
  CX (bi+n+1) 0 :.:
  COP 0 (addOP (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1)) :.:
  invert (addOP (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1)) :.:
  NCX (bi+n+1) 0 :.:
  addOP (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  DEALLOC 1 :.:
  DEALLOC n
  
-- shift
shiftOP :: (Int,Int) -> OP
shiftOP (i,e) =
  LOOP [i..(e-1)] (\k -> SWAP k (k+1))

-- copy a b
copyOP :: Int -> (Int,Int) -> (Int,Int) -> OP
copyOP n (ai,ae) (bi,be) =
  LOOP [0..(n-1)] (\k -> CX (ai+k) (bi+k))

-- timesMod a b m p
timesModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
timesModOP n (ai,ae) (bi,be) (mi,me) (pi,pe) =
  ALLOC n :.: -- carry
  ALLOC n :.: -- t
  LOOP [0..(n-1)] (\i ->
    invert (addOP (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n)) :.:
    CX (ai+2*n) i :.:
    COP i (addOP (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n)) :.: 
    COP (be+2*n-i) (addModOP n (ai+2*n+1,ae+2*n) (pi+2*n,pe+2*n) (mi+2*n,me+2*n)) :.: 
    shiftOP (ai+2*n,ae+2*n) 
  ) :.:
  LOOP [(n-1),(n-2)..0] (\i ->
    invert (shiftOP (ai+2*n,ae+2*n)) :.:
    COP i (invert (addOP (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n))) :.: 
    CX (ai+2*n) i :.:
    addOP (n,2*n-1) (mi+2*n,me+2*n) (ai+2*n,ae+2*n)
  ) :.:
  DEALLOC n :.:
  DEALLOC n

-- squareMod a m s
squareModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
squareModOP n (ai,ae) (mi,me) (si,se) =
  ALLOC n :.: -- t
  copyOP n (ai+n+1,ae+n) (0,n-1) :.:
  timesModOP n (ai+n,ae+n) (0,n-1) (mi+n,me+n) (si+n,se+n) :.:
  invert (copyOP n (ai+n+1,ae+n) (0,n-1)) :.:
  DEALLOC n

-- expMod a b m p e
expModOP :: Int -> Int ->
            (Int,Int) -> (Int,Int) -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
expModOP n k (ai,ae) (bi,be) (mi,me) (pi,pe) (ei,ee)
  | k == 1 =
    NCOP bi (copyOP (n+1) (pi,pe) (ei,ee)) :.:
    COP bi (timesModOP n (ai,ae) (pi,pe) (mi,me) (ei,ee)) 
  | otherwise =
    ALLOC (n+1) :.: -- v
    ALLOC (n+1) :.: -- u
    NCOP (be+d) (copyOP (n+1) (pi+d,pe+d) (n+1,2*n+1)) :.:
    COP (be+d) (timesModOP n (ai+d,ae+d) (pi+d,pe+d) (mi+d,me+d) (ei+d,ee+d)) :.:
    squareModOP n (ai+d,ae+d) (mi+d,me+d) (0,n) :.:
    expModOP n (k-1) (0,n) (bi+d,be+d-1) (mi+d,me+d) (n+1,2*n+1) (ei+d,ee+d) :.:
    invert (squareModOP n (ai+d,ae+d) (mi+d,me+d) (0,n)) :.:
    COP (be+d) (invert (timesModOP n (ai+d,ae+d) (pi+d,pe+d) (mi+d,me+d) (ei+d,ee+d))) :.:
    NCOP (be+d) (invert (copyOP (n+1) (pi+d,pe+d) (n+1,2*n+1))) :.:
    DEALLOC (n+1) :.: 
    DEALLOC (n+1) 
    where d = 2*n + 2

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
addModGen = do n <- chooseInt (2, 20)
               let wn = 3 * n + 1
               as <- vector n
               lowbsms <- suchThat (vector (2*n)) $ \bits ->
                            bools2nat (drop n bits) > max 1 (bools2nat (take n bits))
               return (W wn (fromList (as ++ (False : lowbsms))))

timesModGen :: Gen W
timesModGen = do n <- chooseInt (2, 20)
                 let wn = 4 * n + 2
                 lowasbsms <- suchThat (vector (3*n)) $ \bits ->
                                bools2nat (take n bits) < bools2nat (drop (2*n) bits)
                 let ps = replicate n False 
                 return (W wn (fromList ((False : lowasbsms) ++ (False : ps))))

expModGen :: Gen W
expModGen = do n <- chooseInt (2, 20)
               let wn = 5 * n + 3
               lowas <- suchThat (vector n) $ \bits -> bools2nat bits > 0
               let as = False : lowas
               bs <- vector n
               ms <- suchThat (vector n) $ \bits -> bools2nat bits > 1
               let ps = (replicate n False) ++ [True]
               let es = replicate (n+1) False
               return (W wn (fromList (as ++ bs ++ ms ++ ps ++ es)))

instance Arbitrary W where
--  arbitrary = addGen
--  arbitrary = addModGen
--  arbitrary = timesModGen
  arbitrary = expModGen

addProp :: W -> Bool
addProp w@(W wn vec) =
  let n = (wn - 1) `div` 3
      actual = interp (addOP (0,n-1) (n,2*n-1) (2*n,3*n)) w
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
      actual = interp (addModOP n (0,n-1) (n,2*n) (2*n+1,3*n)) w
      (as,r) = splitAt n (toList vec)
      (bs,ms) = splitAt (n+1) r
      a = bools2nat as
      b = bools2nat bs
      m = bools2nat ms
      sum = if (a + b) >= m then (a + b) - m else (a + b)
      expected = W wn (fromList (as ++ nat2bools (n+1) sum ++ ms))
  in actual == expected 

timesModProp :: W -> Bool
timesModProp w@(W wn vec) =
  let n = (wn - 2) `div` 4
      actual = interp (timesModOP n (0,n) (n+1,2*n) (2*n+1,3*n) (3*n+1,4*n+1)) w
      (as,r) = splitAt (n+1) (toList vec)
      (bs,r') = splitAt n r
      (ms,ps) = splitAt n r'
      a = bools2nat as
      b = bools2nat bs
      m = bools2nat ms
      p = bools2nat ps
      res = (p + b * a) `mod` m
      expected = W wn (fromList (as ++ bs ++ ms ++ nat2bools (n+1) res))
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
      a = bools2nat as
      b = bools2nat bs
      m = bools2nat ms
      p = bools2nat ps
      res = (a ^ b) `mod` m
      expected = W wn (fromList (as ++ bs ++ ms ++ ps ++ nat2bools (n+1) res))
  in actual == expected 

------------------------------------------------------------------------------
------------------------------------------------------------------------------
