module FormulaRepr where

------------------------------------------------------------------------------
-- Interface for formulae representations

-- Each representation differs in how it represents variables and how
-- it represents formulae. Each representation should allow us to
-- produce a formula from a variable

-- We are using an explicit dictionary here, as in actual use it can't
-- be inferred

data FormulaRepr f r = FR 
  { fromVar  :: r -> f
  , fromVars :: Int -> r -> [ f ]
  }
  
------------------------------------------------------------------------------
