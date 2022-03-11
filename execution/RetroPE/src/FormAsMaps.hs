module FormAsMaps where

-- Representation of formulas as xor lists of and maps (of Int)

import Data.List (intercalate,group,sort,sortBy)
import Data.IntSet (IntSet, toAscList, union, empty, singleton)

import Value (Value(..))
import FormulaRepr (FormulaRepr(FR))

----------------------------------------------------------------------------------------
-- Values can static or symbolic formulae
-- Formulae are in "algebraic normal form"

type Literal = Int

-- Ands []      = True
-- Ands [a,b,c] = a && b && c

newtype Ands = Ands { lits :: IntSet }
  deriving (Eq,Ord)

instance Show Ands where
  show as = showL (toAscList $ lits as)
    where showL [] = "1"
          showL ss = concatMap (\x -> 'x' : show x) ss

(&&&) :: Ands -> Ands -> Ands
(Ands lits1) &&& (Ands lits2) = Ands $ union lits1 lits2

(***) :: [Ands] -> [Ands] -> [Ands]
ands1 *** ands2 = [ and1 &&& and2 | and1 <- ands1, and2 <- ands2 ]

-- Formula [] = False
-- Formula [ Ands [], Ands [a], Ands [b,c] ] = True XOR a XOR (b && c)

newtype Formula = Formula { ands :: [Ands]}
  deriving (Eq,Ord)

instance Show Formula where
  show f = showC (ands f)
    where
      showC [] = "0"
      showC cs = intercalate " \\oplus " (map show cs)

mapF :: ([Ands] -> [Ands]) -> Formula -> Formula
mapF f (Formula ands) = Formula (f ands)

mapF2 :: ([Ands] -> [Ands] -> [Ands]) -> Formula -> Formula -> Formula
mapF2 f (Formula ands1) (Formula ands2) = Formula (f ands1 ands2)

(+++) :: Formula -> Formula -> Formula
(Formula ands1) +++ (Formula ands2) = Formula (ands1 ++ ands2)

-- Normalization

-- a && a => a is automatically done by IntSet

-- a XOR a = 0

normalizeAnds :: [Ands] -> [Ands]
normalizeAnds = map head . filter (odd . length) . group . sort -- (sortBy f)

-- Convert to ANF

anf :: Formula -> Formula
anf = mapF normalizeAnds

-- 

false :: Formula
false = Formula []

true :: Formula
true = Formula [ Ands empty ]

isStatic :: Formula -> Bool
isStatic f = f == false || f == true

fromBool :: Bool -> Formula
fromBool False = false
fromBool True  = true

fromVar :: Int -> Formula
fromVar s = Formula [ Ands (singleton s) ]

fromVars :: Int -> Int -> [Formula]
fromVars n base = map (fromVar . (base +)) [0..(n-1)]

--

fnot :: Formula -> Formula
fnot form = anf $ true +++ form

fxor :: Formula -> Formula -> Formula
fxor form1 form2 = anf $ form1 +++ form2

fand :: Formula -> Formula -> Formula
fand form1 form2 = anf $ mapF2 (***) form1 form2

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
