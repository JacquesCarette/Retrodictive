module FormAsBitmaps (
  Formula, lits, ands, formRepr,
  normalize, xor
  ) where

import Data.Bits (bit,(.|.))
import Data.Bits.Bitwise (toListLE)
import Data.List (intercalate, partition, subsequences, sort)
import qualified Data.Map as Map
import qualified Data.MultiSet as MS
import Numeric.Natural

import Value (Value(..))
import FormulaRepr (FormulaRepr(FR))

------------------------------------------------------------------------------
-- Representation of formulas as xor maps of bitmaps
-- Faster than lists of strings

-- Values can static or symbolic formulae
-- Formulae are in "algebraic normal form"

type Literal = Natural

-- Ands 0     = True
-- Ands 01011 = x0 & x1 & x3

newtype Ands = Ands { lits :: Literal }

instance Eq Ands where
  (Ands a1) == (Ands a2) = a1 == a2

{-# INLINABLE compAnds #-}
compAnds :: Ands -> Ands -> Ordering
compAnds (Ands a1) (Ands a2) = compare a1 a2

instance Ord Ands where
  compare = compAnds

instance Show Ands where
  show as = showL $ zip [0..] $ toListLE $ lits as
    where showL :: [(Integer, Bool)] -> String
          showL [] = "1"
          showL ss = foldr (\x s -> if snd x then 'x' : (show (fst x) ++ s) else s) "" ss

-- while this represents an And, this is about presence / absence of variables

(&&&) :: Ands -> Ands -> Ands
(Ands lits1) &&& (Ands lits2) = Ands $ lits1 .|. lits2

-- Formula 0 = False
-- Formula [ Ands 0, Ands 1, Ands 110 ] = True XOR x0 XOR (x1 && x2)

type Occur = Int
-- Raw XOR formulas
type XORFU = Map.Map Ands Occur
-- XOR formulas that are normalized, i.e occur 0 or 1 time
type XORF = MS.MultiSet Ands

newtype Formula = Formula { ands :: XORF }

instance Eq Formula where
  (Formula f1) == (Formula f2) = f1 == f2

-- assumes the Multiset is normalized
instance Show Formula where
  show f = showC (MS.toAscList $ ands f)
    where
      showC [] = "0"
      showC cs = intercalate " \\oplus " (map show cs)

normalizeF :: XORFU -> XORF
normalizeF m = MS.fromOccurMap $ Map.mapMaybe normal m
  where
    normal a = if even a then Nothing else Just 1

--- Cartesian Product

(***) :: XORF -> XORF -> XORF
ands1 *** ands2 = normalizeF mm
  where
    m1 = MS.toMap ands1
    m2 = MS.toMap ands2
    -- cartesian product of maps
    mm :: XORFU
    mm = Map.foldrWithKey (\k a b ->
           Map.foldrWithKey 
             (\k' a' b' -> Map.alter (maybe (Just (a*a')) (\x -> Just ((a*a')+x))) (k &&& k') b')
             b m2) Map.empty m1
         
    {- the following seems to be slower -- all the time is in the fromOccurList
    m3 :: [ (Ands,Int) ]
    m3 = Map.foldrWithKey (\k a b ->
           Map.foldrWithKey (\k' a' b' -> (k &&& k',a*a') : b')
             b m2) [] m1
    mm = MS.toMap $ MS.fromOccurList m3
    -}

mapF :: (XORF -> XORF) -> Formula -> Formula
mapF f (Formula ands) = Formula (f ands)

-- +++ does not normalize
-- 'Xor' of formulas

(+++) :: Formula -> Formula -> Formula
(Formula ands1) +++ (Formula ands2) = Formula (MS.union ands1 ands2)

-- Normalization

-- a && a => a is automatically done by IntSet

-- a XOR a = 0 is kept by having an even OCCUR in XORF

-- Convert to ANF

anf :: Formula -> Formula
anf = mapF (normalizeF . MS.toMap)

-- 

false :: Formula
false = Formula MS.empty

true :: Formula
true = Formula $ MS.singleton $ Ands 0

fromVar :: Int -> Formula
fromVar s = Formula $ MS.singleton $ Ands (bit s)

fromVars :: Int -> Int -> [Formula]
fromVars n base = map (fromVar . (base +)) [0..(n-1)]

--

fnot :: Formula -> Formula
fnot form = anf $ true +++ form

fxor :: Formula -> Formula -> Formula
fxor form1 form2 = anf $ form1 +++ form2

fand :: Formula -> Formula -> Formula
fand form1 form2 = Formula $ ands form1 *** ands form2

--

instance Enum Formula where
  toEnum 0 = false
  toEnum 1 = true
  toEnum _ = error "Internal error: cannot enum symbolic values"
  fromEnum v
    | v == false = 0
    | v == true = 1
    | otherwise = error "Internal error: cannot enum symbolic values"

instance Value Formula where
  zero = false
  one = true
  snot = fnot
  sand = fand
  sxor = fxor

-- instance as explicit dict

formRepr :: FormulaRepr Formula Int
formRepr = FR fromVar fromVars

------------------------------------------------------------------------------
-- We know a lot more when doing expansion of a single gate.
-- Rather than wait for 'downstream' to compute it all, do it now.

normalize :: [Bool] -> [Literal] -> Formula
normalize bs cs = res
  where
    -- pair up the bools and variables, then partition
    -- 'same' are for straight-through variables,
    -- 'nega' for the negated ones
    pairs = zip bs cs
    part = partition fst pairs
    same :: Literal
    same = foldr (.|.) 0 $ map snd $ fst part
    nega :: [ Literal ]
    nega = map snd $ snd part
    -- nega' is then all the subsequences (aka powerset)
    nega' :: [[ Literal ]]
    nega' = subsequences nega
    -- then prepend all the 'same' variables
    res' :: [Ands]
    res' = map Ands $ sort $ map (\x -> same .|. (foldr (.|.) 0 x)) nega'
    -- and finally, make a big xor
    res :: Formula
    res = Formula $ MS.fromDistinctAscList res'

-- Same with xor, especially when we know it's of a single literal
xor :: XORF -> Formula -> Formula
xor i form = 
  if MS.null i then form else Formula $ myxor' (MS.findMin i) m
  where
    m :: XORF
    m = ands form

myxor' :: Ands -> XORF -> XORF
myxor' j m = if MS.member j m then MS.delete j m else MS.insert j m

