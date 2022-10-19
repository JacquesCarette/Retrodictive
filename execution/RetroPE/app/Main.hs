module Main where

import System.TimeIt
import Text.Printf
import Criterion.Main

-- Comment out the appropriate one for running the 'right' test
import QAlgos (deutschJozsaBal4)
import FormAsLists as FL
import FormAsMaps as FM
import FormAsBitmaps as FB
import RunQAlgos (timeRetroDJ)
-- import RunQAlgos (timeRetroGrover')
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
  -} 

  timeRetroDJ FB.formRepr 0 10 deutschJozsaBal4   -- 0.02
  timeRetroDJ FB.formRepr 0 11 deutschJozsaBal4   -- 0.12
  timeRetroDJ FB.formRepr 0 12 deutschJozsaBal4   -- 0.56
  timeRetroDJ FB.formRepr 0 13 deutschJozsaBal4   -- 2.52
  timeRetroDJ FB.formRepr 0 14 deutschJozsaBal4   -- 11.39
  timeRetroDJ FB.formRepr 0 15 deutschJozsaBal4   -- 54.75
  -- mapM_ (retroGrover 5) [0..31]
  -- runRetroGrover' 23 0

  {-
  defaultMain [
    bgroup "RetroGrover" 
      [ bench "List 10"  $ nf (\rep -> head $ words $ show $ timeRetroGrover' rep "x" 10 0) FL.formRepr
      , bench "Map  10"  $ nf (\rep -> head $ words $ show $ timeRetroGrover' rep 0 10 0) FM.formRepr
      , bench "BitM 10"  $ nf (\rep -> head $ words $ show $ timeRetroGrover' rep 0 10 0) FB.formRepr
      , bench "List 12"  $ nf (\rep -> head $ words $ show $ timeRetroGrover' rep "x" 12 0) FL.formRepr
      , bench "Map  12"  $ nf (\rep -> head $ words $ show $ timeRetroGrover' rep 0 12 0) FM.formRepr
      , bench "BitM 12"  $ nf (\rep -> head $ words $ show $ timeRetroGrover' rep 0 12 0) FB.formRepr
      ]
    ]
  -}
{- The above produces
benchmarking RetroGrover/List 10
time                 4.023 ms   (3.992 ms .. 4.052 ms)
                     0.998 R²   (0.995 R² .. 1.000 R²)
mean                 4.051 ms   (4.015 ms .. 4.119 ms)
std dev              158.7 μs   (90.26 μs .. 272.6 μs)
variance introduced by outliers: 21% (moderately inflated)

benchmarking RetroGrover/Map  10
time                 3.155 ms   (3.012 ms .. 3.266 ms)
                     0.991 R²   (0.984 R² .. 0.996 R²)
mean                 2.869 ms   (2.815 ms .. 2.934 ms)
std dev              198.4 μs   (161.1 μs .. 271.2 μs)
variance introduced by outliers: 48% (moderately inflated)

benchmarking RetroGrover/BitM 10
time                 721.0 μs   (706.0 μs .. 737.5 μs)
                     0.995 R²   (0.993 R² .. 0.996 R²)
mean                 774.6 μs   (754.8 μs .. 796.5 μs)
std dev              65.37 μs   (57.23 μs .. 77.02 μs)
variance introduced by outliers: 67% (severely inflated)

benchmarking RetroGrover/List 12
time                 23.22 ms   (22.14 ms .. 24.62 ms)
                     0.992 R²   (0.984 R² .. 0.998 R²)
mean                 24.36 ms   (23.80 ms .. 24.77 ms)
std dev              1.036 ms   (656.9 μs .. 1.394 ms)
variance introduced by outliers: 15% (moderately inflated)

benchmarking RetroGrover/Map  12
time                 16.43 ms   (14.85 ms .. 18.42 ms)
                     0.946 R²   (0.886 R² .. 1.000 R²)
mean                 15.32 ms   (14.93 ms .. 16.68 ms)
std dev              1.534 ms   (558.9 μs .. 3.064 ms)
variance introduced by outliers: 48% (moderately inflated)

benchmarking RetroGrover/BitM 12
time                 5.931 ms   (5.151 ms .. 6.632 ms)
                     0.929 R²   (0.882 R² .. 0.979 R²)
mean                 4.825 ms   (4.655 ms .. 5.144 ms)
std dev              729.0 μs   (433.2 μs .. 1.187 ms)
variance introduced by outliers: 79% (severely inflated)

-}
  -- Shor
  -- runRetroShor (Just 40) Nothing Nothing 21
  -- should be fast: 15, 51, 83, 771; slower: 21, 35
  -- runRetroShor (Just 42) 15 1

  -- Notes for RetroShor:
  -- For 21, 41 and 42 (as seeds) are lucky guesses; 40 'works'
  -- For 15 and 51, 42 is not a lucky guess

------------------------------------------------------------------------------
