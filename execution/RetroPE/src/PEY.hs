module PEY where

import Data.List (intercalate,group,sort)

import Value (Value(..))
import FormulaRepr (FormulaRepr(FR))
import qualified QAlgos as Q

----------------------------------------------------------------------------------------
{--

Approximate the full ANF by only keep track of at most TWO variables
in each AND clause. We will assume that x_{i+1} is more significant
that x_{i} so we will only keep track of the two variables corresponding to
the two most significant bits

--}

type Literal = String

-- Ands []      = True
-- Ands [a,b,c] = a && b && c
-- but only keep on variable in list (msb)

newtype Ands = Ands { lits :: [Literal] }
  deriving (Eq,Ord)

instance Show Ands where
  show as = showL (lits as)
    where showL [] = "1"
          showL ss = concat ss

mapA :: ([Literal] -> [Literal]) -> Ands -> Ands
mapA f (Ands lits) = Ands (f lits)

(&&&) :: Ands -> Ands -> Ands
(Ands []) &&& (Ands ss) = Ands ss
(Ands [s]) &&& (Ands []) = Ands [s]
(Ands [s1]) &&& (Ands [s2]) = Ands [s1,s2]
(Ands [s1,s2]) &&& (Ands []) = Ands [s1,s2]
(Ands ss1) &&& (Ands ss2) = Ands (foldr max2 ["",""] (ss1 ++ ss2))
  where max2 s [m1,m2] | m1 > m2 = [m1, max s m2]
                       | otherwise = [m2, max s m1]

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
      showC cs = intercalate " + " (map show cs)

mapF :: ([Ands] -> [Ands]) -> Formula -> Formula
mapF f (Formula ands) = Formula (f ands)

mapF2 :: ([Ands] -> [Ands] -> [Ands]) -> Formula -> Formula -> Formula
mapF2 f (Formula ands1) (Formula ands2) = Formula (f ands1 ands2)

(+++) :: Formula -> Formula -> Formula
(Formula ands1) +++ (Formula ands2) = Formula (ands1 ++ ands2)

-- Normalization

-- a && a => a

normalizeLits :: [Literal] -> [Literal]
normalizeLits = map head . group . sort 

-- a XOR a = 0

normalizeAnds :: [Ands] -> [Ands]
normalizeAnds = map head . filter (odd . length) . group . sort

-- Convert to ANF

anf :: Formula -> Formula
anf = mapF (normalizeAnds . map (mapA normalizeLits))

-- 

false :: Formula
false = Formula []

true :: Formula
true = Formula [ Ands [] ]

isStatic :: Formula -> Bool
isStatic f = f == false || f == true

fromBool :: Bool -> Formula
fromBool False = false
fromBool True  = true

toBool :: Formula -> Bool
toBool f | f == false = False
         | f == true  = True
         | otherwise  = error "Internal error: converting a complex formula to bool"

fromVar :: String -> Formula
fromVar s = Formula [ Ands [s] ]

fromVars :: Int -> String -> [Formula]
fromVars n s = map fromVar (zipWith (\ s n -> s ++ show n) (replicate n s) [0..(n-1)])

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
formRepr :: FormulaRepr Formula
formRepr = FR fromVar fromVars

----------------------------------------------------------------------------------------
-- Testing

retroShor :: Integer -> IO ()
retroShor = Q.retroShor formRepr

{--
*PEY> retroShor 21
n=9; a=11

1 + x0 + x0x1 + x0x3 + x0x5 + x0x7 + x0x9 + x1 + x1x2 + x1x3 + x1x4 + x1x5 + x1x6 + x1x7 + x1x8 + x1x9 + x2 + x2x3 + x2x4 + x2x5 + x2x6 + x2x7 + x2x8 + x2x9 + x3 + x3x4 + x3x5 + x3x6 + x3x7 + x3x8 + x3x9 + x4 + x4x5 + x4x6 + x4x7 + x4x8 + x4x9 + x5 + x5x6 + x5x7 + x5x8 + x5x9 + x6 + x6x7 + x6x8 + x6x9 + x7 + x7x8 + x7x9 + x8 + x8x9 + x9 = 1

x0 + x0x1 + x0x3 + x0x5 + x0x7 + x0x9 + x1x2 + x1x4 + x1x6 + x1x8 + x2x4 + x2x6 + x2x8 + x3x4 + x3x6 + x3x8 + x4x6 + x4x8 + x5x6 + x5x8 + x6x8 + x7x8 = 0

x0x1 + x0x2 + x0x3 + x0x4 + x0x5 + x0x6 + x0x7 + x0x8 + x0x9 + x1 + x1x2 + x1x4 + x1x6 + x1x8 + x2x4 + x2x6 + x2x8 + x3 + x3x4 + x3x6 + x3x8 + x4x6 + x4x8 + x5 + x5x6 + x5x8 + x6x8 + x7 + x7x8 + x9 = 0

x0x1 + x0x2 + x0x3 + x0x4 + x0x5 + x0x6 + x0x7 + x0x8 + x0x9 + x1x3 + x1x5 + x1x7 + x1x9 + x2x3 + x2x5 + x2x7 + x2x9 + x3x5 + x3x7 + x3x9 + x4x5 + x4x7 + x4x9 + x5x7 + x5x9 + x6x7 + x6x9 + x7x9 + x8x9 = 0

x0x2 + x0x4 + x0x6 + x0x8 + x1x3 + x1x5 + x1x7 + x1x9 + x2 + x2x3 + x2x5 + x2x7 + x2x9 + x3x5 + x3x7 + x3x9 + x4 + x4x5 + x4x7 + x4x9 + x5x7 + x5x9 + x6 + x6x7 + x6x9 + x7x9 + x8 + x8x9 = 0


--}

retroDeutsch = Q.retroDeutsch formRepr

retroDeutschJozsa :: Int -> ([Bool] -> [Bool]) -> IO ()
retroDeutschJozsa = Q.retroDeutschJozsa formRepr

retroBernsteinVazirani :: IO ()
retroBernsteinVazirani = Q.retroBernsteinVazirani formRepr

retroSimon :: IO ()
retroSimon = Q.retroSimon formRepr

retroGrover :: Int -> Integer -> IO ()
retroGrover = Q.retroGrover formRepr

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
