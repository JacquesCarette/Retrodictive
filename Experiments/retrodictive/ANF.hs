module ANF where

import Data.List (intersperse,sort)

--

import Numeric 

----------------------------------------------------------------------------------------
-- Values can static or symbolic formulae
-- Formulae are in "algebraic normal form"

type Literal = String

-- []      = True
-- [a,b,c] = a && b && c

newtype Ands = Ands { lits :: [Literal] }
  deriving (Eq,Ord)

instance Show Ands where
  show as = showL (lits as)
    where showL [] = "1"
          showL ss = concat ss

-- Formula [] = False
-- Formula [[],[a],[b,c]] = True XOR a XOR (b && c)

newtype Formula = Formula { clauses :: [Ands]}
  deriving (Eq,Ord)

instance Show Formula where
  show f = showC (clauses f)
    where
      showC [] = "0"
      showC cs = concat $ intersperse " + " (map show cs)

false :: Formula
false = Formula { clauses = [] }

true :: Formula
true = Formula { clauses = [ Ands [] ] }

isStatic :: Formula -> Bool
isStatic f = f == false || f == true

fromBool :: Bool -> Formula
fromBool False = false
fromBool True = true

toBool :: Formula -> Bool
toBool f | f == false = False
         | f == true = True
         | otherwise = error "Internal error: converting a complex formula to bool"

fromVar :: String -> Formula
fromVar s = Formula { clauses = [ Ands [s] ] }

-- 

-- Remove duplicates from a sorted list of literals

removeDups :: [Literal] -> [Literal]
removeDups [] = []
removeDups [s] = [s]
removeDups (s1 : s2 : ss) 
  | s1 == s2 = removeDups (s2 : ss)
  | otherwise = s1 : removeDups (s2 : ss)

-- Since a & a => a
-- remove redundant formulae from a sorted list

simplifyAnds :: [Ands] -> [Ands]
simplifyAnds [] = []
simplifyAnds [c] = [c]
simplifyAnds (c1 : c2 : cs) 
  | c1 == c2 = simplifyAnds cs
  | otherwise = c1 : simplifyAnds (c2 : cs)

-- Boolean operations on formulae in ANF

snot :: Formula -> Formula
snot f = Formula (simplifyAnds (clauses true ++ clauses f))

sxor :: Formula -> Formula -> Formula
sxor (Formula cs1) (Formula cs2) = Formula (simplifyAnds (sort (cs1 ++ cs2)))

sand :: Formula -> Formula -> Formula
sand (Formula cs1) (Formula cs2) = Formula (simplifyAnds (sort (prod cs1 cs2)))
  where prod cs1 cs2 = [ Ands (removeDups (sort (lits c1 ++ lits c2)))
                       | c1 <- cs1, c2 <- cs2 ]
          
--

type Value = Formula

newValue :: Bool -> Value
newValue = fromBool

newDynValue :: String -> Value
newDynValue = fromVar

valuesToInt :: [Value] -> Integer
valuesToInt = toInt . map toBool

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

