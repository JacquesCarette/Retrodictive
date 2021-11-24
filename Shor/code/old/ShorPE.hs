module ShorPE where

import Data.Char
import GHC.Integer.GMP.Internals
import Data.Vector (Vector, fromList, toList, (!), (//))
import qualified Data.Vector as V 
import System.Random

import Text.Printf

------------------------------------------------------------------------------
-- Interpretations

type Var = Int

data Bit = Bool Bool | BitVar Var | NotBitVar Var
  deriving Eq

data Formula =
    Bit Bit
  | CXForm Formula Formula
  deriving (Eq,Show)

data WVar = WVar Int (Vector Formula) deriving Eq

low,high :: Bit
low = Bool False
high = Bool True

notForm :: Formula -> Formula
notForm (Bit (Bool b)) = Bit (Bool (not b))
notForm (Bit (BitVar v)) = Bit (NotBitVar v)
notForm (Bit (NotBitVar v)) = Bit (BitVar v)
--- ...

instance Show Bit where
  show (Bool True) = "True"
  show (Bool False) = "False"
  show (BitVar v) = show v
  show (NotBitVar v) = "-" ++ show v

instance Show WVar where
  show (WVar n vec) =
    printf "\t[%d] %s" n (concat (V.map show  vec))

class (Monad m) => Circuit m where
  cx  :: Int -> Int -> WVar -> m WVar
{--
  ncx :: Int -> Int -> WVar -> m WVar
  ccx :: Int -> Int -> Int -> WVar -> m WVar
  ...
--}

(>->) :: Circuit m => (a -> m b) -> (b -> m c) -> (a -> m c)
(f >-> g) a = 
    do b <- f a
       g b

compose :: Circuit m => [a -> m a] -> (a -> m a)
compose = foldr (>->) return

notIVar :: Vector Formula -> Int -> Vector Formula
notIVar vec i = vec // [(i , notForm (vec ! i))]

------------------------------------------------------------------------------
-- PE / Interpreter

data R a = R a

instance Functor R where
  fmap f (R a) = R (f a)

instance Applicative R where
  pure = R
  (R f) <*> (R a) = R (f a)

instance Monad R where
  return = R
  (R e1) >>= e2 = e2 e1

instance Circuit R where
  cx i j w@(WVar n vec)
    | vec ! i == Bit (Bool True)  = return (WVar n (notIVar vec j))
    | vec ! i == Bit (Bool False) = return w
    -- perhaps specialize CX (CX i j) k etc
    | otherwise = return (WVar n (vec // [(j, CXForm (vec ! i) (vec ! j))]))

{--
interp op w@(W n vec) = 
  case op of                         

    CX i j | vec ! i ->
      W n (notI vec j)
    CX _ _ -> w

    NCX i j | not (vec ! i) ->
      W n (notI vec j)
    NCX _ _ -> w

    CCX i j k | vec ! i && vec ! j -> 
      W n (notI vec k)
    CCX _ _ _ -> w
--}



{--
        | COP Int OP                       -- if first true; apply op
        | NCOP Int OP                      -- if first false; apply op
        | SWAP Int Int                     -- swap values at given indices
        | (:.:) OP OP                      -- sequential composition
        | ALLOC Int                        -- alloc n bits to front
        | DEALLOC Int                      -- dealloc n bits from front
        | LOOP [Int] (Int -> OP)           -- apply fun to each of indices
--}  

------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
------------------------------------------------------------------------------
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
       
-- count number of primitive operations

size :: OP -> Int
size (CX i j)         = 1
size (NCX i j)        = 1
size (CCX i j k)      = 1
size (COP i op)       = size op
size (NCOP i op)      = size op
size (SWAP i j)       = 1
size (op1 :.: op2)    = size op1 + size op2
size (ALLOC i)        = 1
size (DEALLOC i)      = 1
size (LOOP indices f) = size (f 0) * length indices

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

toInt :: Vector Bool -> Integer
toInt bs = V.foldr (\b n -> toInteger (fromEnum b) + 2*n) 0 (V.reverse bs)

fromInt :: Int -> Integer -> Vector Bool
fromInt len n = V.replicate (len - length bits) False V.++ fromList bits
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
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
      W n (notI vec j)
    CX _ _ -> w

    NCX i j | not (vec ! i) ->
      W n (notI vec j)
    NCX _ _ -> w

    CCX i j k | vec ! i && vec ! j -> 
      W n (notI vec k)
    CCX _ _ _ -> w

    COP i op | vec ! i ->
      interp op w
    COP _ _ -> w

    NCOP i op | not (vec ! i) ->
      interp op w
    NCOP _ _ -> w

    SWAP i j ->
      W n (vec // [ (i , vec ! j), (j , (vec ! i)) ])

    op1 :.: op2 -> 
      interp op2 (interp op1 w)

    ALLOC i -> 
      W (n+i) (V.replicate i False V.++ vec)

    DEALLOC i ->
      W (n-i) (V.drop i vec)

    LOOP indices f -> 
      loop indices w
        where loop [] w = w
              loop (i:is) w = loop is (interp (f i) w)

------------------------------------------------------------------------------
-- Circuits following Ch.6 of:
-- Quantum Computing: A Gentle Introduction by Rieffel & Polak

-- sum: c, a, b => c, a, (a+b+c) mod 2

sumOP :: Int -> Int -> Int -> OP
sumOP c a b =
  CX a b :.:
  CX c b

-- carry: c, a, b, c' => c, a, b, c' xor F(a,b,c)
-- where F(a,b,c) = 1 if two or more inputs are 1

carryOP :: Int -> Int -> Int -> Int -> OP
carryOP c a b c' =
  CCX a b c' :.:
  CX a b :.:
  CCX c b c' :.:
  CX a b

-- takes n-bits [a, b, c, ... , y, z] stored in the range (i,e)
-- and produces [b, c, ... , y, z, a]
--
-- when a=0, this is multiplication by 2

shiftOP :: (Int,Int) -> OP
shiftOP (i,e) =
  LOOP [i..(e-1)] (\k -> SWAP k (k+1))

-- a has n-bits stored in the range (ai,ae)
-- b has n-bits stored in the range (bi,be)

-- copy: a , b => a, a XOR b

copyOP :: Int -> (Int,Int) -> (Int,Int) -> OP
copyOP n (ai,ae) (bi,be) =
  LOOP [0..(n-1)] (\k -> CX (ai+k) (bi+k))

------------------------------------------------------------------------------
-- Addition of n-bit numbers

-- c has n-bits stored in the range (ci,ce) inclusive
--   initialized to 0
-- a has n-bits stored in the range (ai,ae)
-- b has (n+1)-bits stored in the range (bi,be)

-- add:  0, a, b => 0, a, (a + b) `mod` (2 ^ (n+1))
-- unAdd:  0, a, b => 0, a, (b - a) (+ 2 ^ (n+1) if (b-a) negative)

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

------------------------------------------------------------------------------
-- Addition of n-bit numbers modulo another n-bit number

-- a has n-bits stored in the range (ai,ae)
-- b has (n+1)-bits stored in the range (bi,be)
-- m has n-bits stored in the range (mi,me)
-- precondition: a < m and b < m and m > 0 to make sense of mod

-- addMod: a, b, m => a, (a+b) `mod` m, m
-- unAddMod: a, b, m => a, (b-a)*, m where we add m to (b-a) if negative

addModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
addModOP n (ai,ae) (bi,be) (mi,me) = 
  ALLOC n :.: -- carry
  ALLOC 1 :.: -- t
  addOP n (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  invert (addOP n (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1)) :.:
  CX (bi+n+1) 0 :.:
  COP 0 (addOP n (1,n) (mi+n+1,me+n+1) (bi+n+1,be+n+1)) :.:
  invert (addOP n (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1)) :.:
  NCX (bi+n+1) 0 :.:
  addOP n (1,n) (ai+n+1,ae+n+1) (bi+n+1,be+n+1) :.:
  DEALLOC 1 :.:
  DEALLOC n

------------------------------------------------------------------------------
-- Multiply two n-bit numbers mod another n-bit number

-- a has (n+1)-bits stored in the range (ai,ae)
-- b has (n+1)-bits stored in the range (bi,be)
-- m has n-bits stored in the range (mi,me)
-- p has (n+1)-bits stored in the range (pi,pe)
-- precondition: a < m, p < m, and m > 0 to make sense of mod

-- timesMod: a, b, m, p => a, b, m, (p + ab) `mod` m
-- unTimesMod: a, b, m, p => a, b, m, (p - ab `mod` m) (add m if negative)

timesModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
timesModOP n (ai,ae) (bi,be) (mi,me) (pi,pe) =
  ALLOC n :.: -- carry
  ALLOC (n+1) :.: -- t
  LOOP [0..n] (\i ->
    invert (addOP n (n+1,2*n) (mi+d,me+d) (ai+d,ae+d)) :.:
    CX (ai+d) i :.:
    COP i (addOP n (n+1,2*n) (mi+d,me+d) (ai+d,ae+d)) :.: 
    COP (be+d-i) (addModOP n (ai+d+1,ae+d) (pi+d,pe+d) (mi+d,me+d)) :.: 
    shiftOP (ai+d,ae+d) 
  ) :.:
  LOOP [n,(n-1)..0] (\i ->
    invert (shiftOP (ai+d,ae+d)) :.:
    COP i (invert (addOP n (n+1,2*n) (mi+d,me+d) (ai+d,ae+d))) :.: 
    CX (ai+d) i :.:
    addOP n (n+1,2*n) (mi+d,me+d) (ai+d,ae+d)
  ) :.:
  DEALLOC (n+1) :.:
  DEALLOC n
  where d = 2 * n + 1

------------------------------------------------------------------------------
-- Square mod n
-- Special case of multiplication

-- a has (n+1)-bits stored in the range (ai,ae)
-- m has n-bits stored in the range (mi,me)
-- s has (n+1)-bits stored in the range (si,se)
-- precondition: a < m, s < m, and m > 0 to make sense of mod

-- squareMod: a, m, s => a, m, (s + a^2) `mod` m
-- unSquareMod: a, m, s => a, m, (s - a^2 `mod` m) (add m if negative)

squareModOP :: Int -> (Int,Int) -> (Int,Int) -> (Int,Int) -> OP
squareModOP n (ai,ae) (mi,me) (si,se) =
  ALLOC (n+1) :.: -- t
  copyOP (n+1) (ai+d,ae+d) (0,n) :.:
  timesModOP n (ai+d,ae+d) (0,n) (mi+d,me+d) (si+d,se+d) :.:
  invert (copyOP (n+1) (ai+d,ae+d) (0,n)) :.:
  DEALLOC (n+1)
  where d = n + 1

------------------------------------------------------------------------------
-- ExpMod mod n

-- a has (n+1)-bits stored in the range (ai,ae)
-- b has n-bits stored in the range (bi,be)
-- m has n-bits stored in the range (mi,me)
-- p has (n+1)-bits stored in the range (pi,pe)
-- e has (n+1)-bits stored in the range (ei,ee)
-- precondition: 0 < a < m, p < m, e < m, and m > 1

-- expMod : a, b, m, p, e => a, b, m, p, e XOR p(a^b) `mod` m
-- unExpMod : a, b, m, p, e => a, b, m, 1, e XOR p(a^b) `mod` m

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
-- Factoring...

factor :: Integer -> IO (Integer,Integer)
factor n =
  do x <- randomRIO (2, n - 1)
     let f r = expModOP     -- for x ^ r `mod` n
                 undefined
                 undefined
                 undefined
                 undefined
                 undefined
                 undefined
                 undefined
     test <- randomRIO (0, n * n)
     let observe = interp (f test)
     let final = undefined
                 -- extract the relevant bits from observe
                 -- and build symbolic data for rest
     let inp = interp (invert (f undefined))
                 -- r undefined and symbolic and includes some information from final 
     return undefined -- post process inp

------------------------------------------------------------------------------
