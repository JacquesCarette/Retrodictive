module FormulaRepr where

-- representing formulas
 

----------------------------------------------------------------------------------------

-- We're going to use an explicit dictionary here, as in actual use it can't be
-- inferred

data FormulaRepr f = FR 
  { fromVar :: String -> f
  , fromVars :: Int -> String -> [ f ]
  }

----------------------------------------------------------------------------------------
