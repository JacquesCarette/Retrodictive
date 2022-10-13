module BoolUtils where
  
------------------------------------------------------------------------------

-- Interpret a list of booleans as an Integer
toInt :: [Bool] -> Integer
toInt = foldr (\ b n -> toInteger (fromEnum b) + 2*n) 0

------------------------------------------------------------------------------
