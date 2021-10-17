{-# OPTIONS_GHC -XGADTs -XTypeOperators #-}

module Shor where

-----------------------------------------------------------------------------
-- Goal is to define reversible version of a^x mod N
-- Devise a reversible language for just this task

data a :<=> b where 
  Id    :: a :<=> a
  (:.:) :: (a :<=> b) -> (b :<=> c) -> (a :<=> c)
  (:*:) :: (a :<=> b) -> (c :<=> d) -> ((a,c) :<=> (b,d))
  CommuteTimes :: (a,b) :<=> (b,a) 
  AssocTimesL  :: (a,(b,c)) :<=> ((a,b),c)
  AssocTimesR  :: ((a,b),c) :<=> (a,(b,c))
  Even :: (Integer,Bool) :<=> (Integer,Bool)
  Div2L :: (Integer,Integer) :<=> (Integer,Integer)
  Div2R :: (Integer,Integer) :<=> (Integer,Integer)
  MultModL :: (Integer,Integer,Integer,Integer) :<=> (Integer,Integer,Integer,Integer) 
  MultModR :: (Integer,Integer,Integer,Integer) :<=> (Integer,Integer,Integer,Integer)

interp :: (a :<=> b) -> a -> b
interp Id v = v
interp (c1 :.: c2) v = interp c2 (interp c1 v)
interp (c1 :*: c2) (v1 , v2) = (interp c1 v1 , interp c2 v2)
interp CommuteTimes (v1 , v2) = (v2 , v1)
interp AssocTimesL (v1 , (v2 , v3)) = ((v1 , v2) , v3)
interp AssocTimesR ((v1 , v2) , v3) = (v1 , (v2 , v3))
interp Even (n , b) = (n , b /= (n `mod` 2 == 0))
interp Div2L (n , h) = (n , h + (n `div` 2))
interp Div2R (n , h) = (n , h - (n `div` 2))
interp MultModL (a, b, m, h) = (a, b, m, h + ((a * b) `mod` m))
interp MultModR (a, b, m, h) = (a, b, m, h - ((a * b) `mod` m))

{--

https://byorgey.wordpress.com/2020/02/15/
	competitive-programming-in-haskell-modular-arithmetic-part-1/

modexp :: Integer -> Integer -> Integer -> Integer
modexp _ 0 _ = 1
modexp a x m
  | even x    = (r*r) `mod` m
  | otherwise = (a*r*r) `mod` m
  where
    r = modexp a (x `div` 2) m


Expand for a=8, m=15

modexp x
  | even x    = (r*r) `mod` 15
  | otherwise = (8*r*r) `mod` 15
  where
    r = modexp 8 (x `div` 2) 15

--}

-----------------------------------------------------------------------------
-- Tests

-----------------------------------------------------------------------------

