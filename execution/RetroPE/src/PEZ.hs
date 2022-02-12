module PEZ where

-- partial evaluation of a circuit in the Z basis (the computational basis)

import Data.List (intercalate,group,sort)

import Value (Value(..))
import FormulaRepr (FormulaRepr(FR))
import qualified QAlgos as Q

----------------------------------------------------------------------------------------
-- Values can static or symbolic formulae
-- Formulae are in "algebraic normal form"

type Literal = String

-- Ands []      = True
-- Ands [a,b,c] = a && b && c

newtype Ands = Ands { lits :: [Literal] }
  deriving (Eq,Ord)

instance Show Ands where
  show as = showL (lits as)
    where showL [] = "1"
          showL ss = concat ss

mapA :: ([Literal] -> [Literal]) -> Ands -> Ands
mapA f (Ands lits) = Ands (f lits)

(&&&) :: Ands -> Ands -> Ands
(Ands lits1) &&& (Ands lits2) = Ands (lits1 ++ lits2)

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

fromVar :: String -> Formula
fromVar s = Formula [ Ands [s] ]

fromVars :: Int -> String -> [Formula]
fromVars n s = map fromVar (map (\ n -> s ++ show n) [0..(n-1)])

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

retroDeutsch = Q.retroDeutsch formRepr

{--

*PEZ> retroDeutsch Q.deutsch0
0

*PEZ> retroDeutsch Q.deutsch1
1

*PEZ> retroDeutsch Q.deutschId
x

*PEZ> retroDeutsch Q.deutschNot
1 + x

--}

retroDeutschJozsa :: Int -> ([Bool] -> [Bool]) -> IO ()
retroDeutschJozsa = Q.retroDeutschJozsa formRepr

{--

*PEZ> retroDeutschJozsa 5 Q.deutschJozsaConstant0
0

*PEZ> retroDeutschJozsa 5 Q.deutschJozsaConstant1
1

*PEZ> retroDeutschJozsa 6 Q.deutschJozsaBal1
x0

*PEZ> retroDeutschJozsa 6 Q.deutschJozsaBal2
x0 + x1 + x2 + x3 + x4 + x5

*PEZ> retroDeutschJozsa 6 Q.deutschJozsaBal3
x0x1x2 + x0x1x2x3x4 + x0x1x2x3x5 + x0x1x2x4 + x0x1x2x4x5 + x0x1x3x4 + x0x1x3x5 + x0x1x4 + x0x1x4x5 + x0x2 + x0x2x3x5 + x0x2x4x5 + x0x3 + x0x3x4x5 + x0x3x5 + x1x2x3x5 + x1x2x4x5 + x1x3x4x5 + x1x3x5 + x1x5 + x2x3x4x5 + x2x3x5 + x2x4 + x3x4x5 + x3x5

--}

-- Shor

retroShor :: Integer -> IO ()
retroShor = Q.retroShor formRepr 

{--

retroShor 15:
circuit has 56,538 gates

----------------------------------------------------
n=8; a=13

1 + x0x1 + x1 = 1
x0 + x0x1 = 0
x0 + x0x1 + x1 = 0
x0x1 = 0

----------------------------------------------------
n=8; a=11

x0 = 0

----------------------------------------------------
n=8; a=8

1 + x0 + x0x1 + x1 = 1
x0 + x0x1 = 0
x0x1 + x1 = 0
x0x1 = 0

----------------------------------------------------
n=8; a=4

1 + x0 = 1
x0 = 0

----------------------------------------------------

--}

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
