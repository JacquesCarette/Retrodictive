module VarInFormula where

------------------------------------------------------------------------------
-- Interface for representing variables in formulas

-- Each representation differs in how it represents variables and how
-- it represents formulae. Each representation should allow us to
-- produce a formula from a variable

-- We are using an explicit dictionary here, as in actual use it can't
-- be inferred

data VarInFormula f{-ormula-} v{-ar repr-} = FR 
  { fromVar  :: v -> f
  , fromVars :: Int -> v -> [ f ]
  }
  
------------------------------------------------------------------------------
