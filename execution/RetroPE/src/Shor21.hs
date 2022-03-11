module Shor21 where

-- PEZ with special optimizations for Shor21
-- first period = 3, so we don't need 9 qubits
-- we need 2 qubits for ancilla and 3 or 4 for computational register

import Data.List (intercalate,group,sort,sortBy)

import Value (Value(..))
import FormulaRepr (FormulaRepr(FR))
import qualified QAlgos as Q


import Text.Printf

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
      showC cs = intercalate " \\oplus " (map show cs)

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
normalizeAnds = map head . filter (odd . length) . group . sort -- (sortBy f)
  where f (Ands xs) (Ands ys) = compare (length xs) (length ys)

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
fromVars n s = map (fromVar . (\ n -> s ++ "_" ++ show n)) [0..(n-1)]

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

-- Shor

retroShor :: Integer -> IO ()
retroShor = Q.retroShor formRepr 

retroShorp :: Integer -> Int -> IO ()
retroShorp = Q.retroShorp formRepr Nothing

retroShorn :: Integer -> Int -> Integer -> IO ()
retroShorn = Q.retroShorn formRepr 

{--
shor 21  with n=5 and a=16

1 \oplus x_0 \oplus x_0x_2 \oplus x_0x_2x_3 \oplus x_0x_2x_3x_4 \oplus x_0x_2x_3x_4x_5 \oplus x_0x_2x_4x_5 \oplus x_0x_2x_5 \oplus x_0x_3x_4 \oplus x_0x_3x_5 \oplus x_0x_4 \oplus x_0x_4x_5 \oplus x_2 \oplus x_2x_3x_4 \oplus x_2x_3x_5 \oplus x_2x_4 \oplus x_2x_4x_5 \oplus x_3 \oplus x_3x_4x_5 \oplus x_3x_5 \oplus x_4 \oplus x_5 = 1

x_0 \oplus x_0x_2x_3 \oplus x_0x_2x_3x_4x_5 \oplus x_0x_2x_3x_5 \oplus x_0x_2x_4 \oplus x_0x_2x_5 \oplus x_0x_3 \oplus x_0x_3x_4 \oplus x_0x_3x_4x_5 \oplus x_0x_4x_5 \oplus x_0x_5 \oplus x_2 \oplus x_2x_3 \oplus x_2x_3x_4 \oplus x_2x_3x_4x_5 \oplus x_2x_4x_5 \oplus x_2x_5 \oplus x_3x_4 \oplus x_3x_5 \oplus x_4 \oplus x_4x_5 = 0

x_0x_2 \oplus x_0x_2x_3x_4 \oplus x_0x_2x_3x_5 \oplus x_0x_2x_4 \oplus x_0x_2x_4x_5 \oplus x_0x_3 \oplus x_0x_3x_4x_5 \oplus x_0x_3x_5 \oplus x_0x_4 \oplus x_0x_5 \oplus x_2x_3 \oplus x_2x_3x_4x_5 \oplus x_2x_3x_5 \oplus x_2x_4 \oplus x_2x_5 \oplus x_3 \oplus x_3x_4 \oplus x_3x_4x_5 \oplus x_4x_5 \oplus x_5 = 0


--}

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------