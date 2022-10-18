module Main where

import System.TimeIt
import Text.Printf

-- Comment out the appropriate one for running the 'right' test
import QAlgos (deutschJozsaBal1)
import RunQAlgos (timeRetroDJ)
import FormAsLists as FL
import FormAsMaps as FM
import FormAsBitmaps as FB
-- import RunQAlgos (runRetroGrover')
-- import RunQAlgos (runRetroShor)

------------------------------------------------------------------------------

main :: IO ()
main = do
  -- Deutsch-Jozsa (takes a size and a function)
  -- For running deutschJozsaBal3 (unfortunately is instantaneous)
  {-
  timeRetroDJ FL.formRepr "x" 6 deutschJozsaBal3
  timeRetroDJ FM.formRepr 0 6 deutschJozsaBal3
  timeRetroDJ FB.formRepr 0 6 deutschJozsaBal3
  -}
  {-
  timeRetroDJ FL.formRepr "x" 10 deutschJozsaBal2 -- 0.03
  timeRetroDJ FM.formRepr 0 10 deutschJozsaBal2   -- 0.04
  timeRetroDJ FB.formRepr 0 10 deutschJozsaBal2   -- 0.03
  timeRetroDJ FL.formRepr "x" 11 deutschJozsaBal2 -- 0.14
  timeRetroDJ FM.formRepr 0 11 deutschJozsaBal2   -- 0.14
  timeRetroDJ FB.formRepr 0 11 deutschJozsaBal2   -- 0.14
  timeRetroDJ FL.formRepr "x" 12 deutschJozsaBal2 -- 0.63
  timeRetroDJ FM.formRepr 0 12 deutschJozsaBal2   -- 0.59
  timeRetroDJ FB.formRepr 0 12 deutschJozsaBal2   -- 0.67
  timeRetroDJ FL.formRepr "x" 13 deutschJozsaBal2 -- 2.78
  timeRetroDJ FM.formRepr 0 13 deutschJozsaBal2   -- 3.85
  timeRetroDJ FB.formRepr 0 13 deutschJozsaBal2   -- 3.25
  timeRetroDJ FL.formRepr "x" 14 deutschJozsaBal2 -- 12.29
  timeRetroDJ FM.formRepr 0 14 deutschJozsaBal2   -- 11.20
  timeRetroDJ FB.formRepr 0 14 deutschJozsaBal2   -- 11.23
  timeRetroDJ FL.formRepr "x" 15 deutschJozsaBal2 -- 53.64
  timeRetroDJ FM.formRepr 0 15 deutschJozsaBal2   -- 55.20
  timeRetroDJ FB.formRepr 0 15 deutschJozsaBal2   -- 55.63
  -} 
  timeRetroDJ FL.formRepr "x" 10 deutschJozsaBal1 -- 0.02
  timeRetroDJ FM.formRepr 0 10 deutschJozsaBal1   -- 0.02
  timeRetroDJ FB.formRepr 0 10 deutschJozsaBal1   -- 0.02
  timeRetroDJ FL.formRepr "x" 11 deutschJozsaBal1 -- 0.13
  timeRetroDJ FM.formRepr 0 11 deutschJozsaBal1   -- 0.13
  timeRetroDJ FB.formRepr 0 11 deutschJozsaBal1   -- 0.13
  timeRetroDJ FL.formRepr "x" 12 deutschJozsaBal1 -- 0.58
  timeRetroDJ FM.formRepr 0 12 deutschJozsaBal1   -- 0.60
  timeRetroDJ FB.formRepr 0 12 deutschJozsaBal1   -- 0.62
  timeRetroDJ FL.formRepr "x" 13 deutschJozsaBal1 -- 2.62
  timeRetroDJ FM.formRepr 0 13 deutschJozsaBal1   -- 2.76
  timeRetroDJ FB.formRepr 0 13 deutschJozsaBal1   -- 2.70
  timeRetroDJ FL.formRepr "x" 14 deutschJozsaBal1 -- 12.96
  timeRetroDJ FM.formRepr 0 14 deutschJozsaBal1   -- 12.35
  timeRetroDJ FB.formRepr 0 14 deutschJozsaBal1   -- 13.42
  timeRetroDJ FL.formRepr "x" 15 deutschJozsaBal1 -- 57.55
  timeRetroDJ FM.formRepr 0 15 deutschJozsaBal1   -- 59.79
  timeRetroDJ FB.formRepr 0 15 deutschJozsaBal1   -- 60.25
  -- mapM_ (retroGrover 5) [0..31]
  -- runRetroGrover' 23 0
  {-
  mapM_ grover [0..28]
  where
    grover n = do
      printf "n = %d\t" n
      timeIt (runRetroGrover' n (min 10 (2^n - 1)))
  -}

  -- Shor
  -- runRetroShor (Just 40) Nothing Nothing 21
  -- should be fast: 15, 51, 83, 771; slower: 21, 35
  -- runRetroShor (Just 42) 15 1

  -- Notes for RetroShor:
  -- For 21, 41 and 42 (as seeds) are lucky guesses; 40 'works'
  -- For 15 and 51, 42 is not a lucky guess

------------------------------------------------------------------------------
