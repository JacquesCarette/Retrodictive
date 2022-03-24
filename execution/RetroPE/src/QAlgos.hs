{-# LANGUAGE ViewPatterns #-}

module QAlgos where

import Data.STRef (readSTRef,writeSTRef)
import Data.List (intercalate,group,sort,sortBy)
import Data.Sequence (fromList)

import Control.Monad.ST (runST,ST)
import Control.Monad.IO.Class (MonadIO)

import System.Random.Stateful (uniformRM, newIOGenM, mkStdGen, getStdGen, newAtomicGenM, globalStdGen, applyAtomicGen, AtomicGenM, StdGen)

import Numeric (readHex)
import GHC.Show (intToDigit)
import Text.Printf (printf)

import Value (Var, Value(..), newVar, newVars, fromInt)
import Circuits (Circuit(..), cx, ccx, cncx, showSizes, sizeOP, OP)
import ArithCirc (expm)
import PE (run)
import Synthesis (synthesis)
import FormulaRepr (FormulaRepr(..))
import QNumeric (toInt)

----------------------------------------------------------------------------------------
-- Helper routine to print out the results

printResult :: (Foldable t, Show a, Show b) => (t (a,b), [(Int,Int)]) -> IO ()
printResult (eqs,sizes) = do
  putStrLn $ showSizes sizes
  mapM_ (\(r,v) ->
    let sr = show r
        sv = show v
    in if sr == sv then return () else 
      printf "%s = %s\n" sr sv)
    eqs

-- Random numbers

mkGen :: Maybe Int -> IO (AtomicGenM StdGen)
mkGen Nothing = return globalStdGen
mkGen (Just i) = newAtomicGenM (mkStdGen i)

----------------------------------------------------------------------------------------
-- Generic quantum oracle construction

viewL :: [a] -> ([a],a)
viewL xs = (init xs, last xs)

uf :: ([Bool] -> Bool) -> ([Bool] -> [Bool])
uf f (viewL -> (xs,y)) = xs ++ [f xs /= y]

-- Quantum algorithms

-- Shor

setupCirc :: Value f => -- invariant: cc is of 'size' n
    FormulaRepr f r -> r -> Int -> Integer -> Circuit s f -> ST s () 
setupCirc fr base n r circ = do
  mapM_ (uncurry writeSTRef) (zip (ancillaOuts circ) (fromInt (n+1) r))
  mapM_ (uncurry writeSTRef) (zip (xs circ) (fromVars fr (n+1) base))

peExpMod :: (Show f, Value f) =>
            FormulaRepr f r -> r -> Int -> Integer -> Integer -> Integer -> 
            ST s ([(f,f)], [(Int,Int)])
peExpMod fr base n a m r = do
  circ <- expm n a m
  setupCirc fr base n r circ
  run circ
  result <- mapM readSTRef (ancillaIns circ)
  let eqs = zip result (ancillaVals circ)
  return (eqs, sizeOP $ op circ)

peExpModp :: (Show f, Value f) =>
    FormulaRepr f r -> r -> Int -> Integer -> Integer -> Integer -> Int -> ST s ([(f,f)], [(Int,Int)])
peExpModp fr base n a m r i = do
  circ <- expm n a m
  setupCirc fr base n r circ
  writeSTRef ((xs circ) !! i) zero
  run circ
  result <- mapM readSTRef (ancillaIns circ)
  let eqs = zip result (ancillaVals circ)
  return (eqs, sizeOP $ op circ)

-- pick observed ancilla

retroShorp :: (Show f, Value f) => FormulaRepr f r -> r -> Maybe Int -> Integer -> Int -> IO ()
retroShorp fr base seed m i = do
      gen <- mkGen seed
      a <- uniformRM (2,m-1) gen
      let n = ceiling $ logBase 2 (fromInteger m * fromInteger m)
      let gma = gcd m a 
      if gma /= 1 
        then putStrLn (printf "Lucky guess %d = %d * %d\n" m gma (m `div` gma))
        else do putStrLn (printf "n=%d; a=%d\n" n a)
                let res = runST $ peExpModp fr base n a m 1 i
                printResult res

-- pick number of bits and 'a'

retroShorn :: (Show f, Value f) => FormulaRepr f r -> r -> Integer -> Int -> Integer -> IO ()
retroShorn fr base m n a = do
      let gma = gcd m a 
      if gma /= 1 
        then putStrLn (printf "Lucky guess %d = %d * %d\n" m gma (m `div` gma))
        else do putStrLn (printf "n=%d; a=%d\n" n a)
                let res = runST $ peExpModp fr base n a m 1 1
                printResult res

retroShor :: (Show f, Value f) => FormulaRepr f r -> r -> Integer -> IO ()
retroShor fr base m = retroShorp fr base Nothing m 1

-- Shor 21 optimized

retroShor21 :: (Show f, Value f) =>
               FormulaRepr f r -> r -> Integer -> IO ()
retroShor21 fr base w = print $ runST $ do
  cs <- newVars (fromVars fr 3 base)
  qs <- newVars (fromInt 2 w)
  run Circuit { op = op (cs !! 0) (cs !! 1) (cs !! 2) (qs !! 0) (qs !! 1)
              , xs = cs
              , ancillaIns = qs
              , ancillaOuts = qs
              , ancillaVals = undefined
              }
  mapM readSTRef qs
  where
    op c0 c1 c2 q0 q1 = fromList
      [ cx c2 q1
      , cx c1 q1
      , cx q1 q0
      , ccx c1 q0 q1
      , cx q1 q0
      , cncx c0 q1 q0
      , cx q1 q0
      , ccx c0 q0 q1
      , cx q1 q0
      ]

{--

Q.retroShor21 FL.formRepr "x" 0
x0 + x0x1 = 0
x0x1 + x1 + x2 = 0
  x0=0, x1=x2 => 000, 011
  x0=1, x1=1, x2=0 => 110
using qutrits:
  x0=0, x2=0 => 000, 010, 020

Q.retroShor21 FL.formRepr "x" 1
1 + x0 + x1 = 0
x0 + x2 = 0
  x0/=x1, x0=x2 => 010, 101
using qutrits
  x0=0, x2=2 => 002, 012 (022)

Q.retroShor21 FL.formRepr "x" 2
x0x1 + x1 = 0
1 + x0 + x0x1 + x2 = 0
  x0=0, x1=0, x2=1 => 001
  x0=1, x1=0, x2=0 => 100
  x0=1, x1=1, x2=1 => 111
using qutrits
  x0=0, x2=1 => 001, 011, 021


--}


-- Deutsch

deutschId, deutschNot, deutsch0, deutsch1 :: [Bool] -> [Bool]
deutschId [x,y]  = [x,y /= x]
deutschNot [x,y] = [x,y /= not x]
deutsch0 [x,y]   = [x,y]
deutsch1 [x,y]   = [x,not y]

retroDeutsch :: (Show f, Value f) => FormulaRepr f r -> r -> ([Bool] -> [Bool]) -> IO ()
retroDeutsch fr base f = print $ runST $ do
  x <- newVar (fromVar fr base)
  y <- newVar zero
  run Circuit { op = synthesis 2 [x,y] f
              , xs = [x]
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

-- Deutsch Jozsa

deutschJozsaConstant0, deutschJozsaConstant1 :: [Bool] -> [Bool]
deutschJozsaBal1, deutschJozsaBal2, deutschJozsaBal3 :: [Bool] -> [Bool]
-- f(x) = 0
deutschJozsaConstant0 = uf (const False)
-- f(x) = 1
deutschJozsaConstant1 = uf (const True)
-- f(x0x1x2..) = x0
deutschJozsaBal1 = uf head
-- f(x0x1x2..) = xor(x0,x1,x2...)
deutschJozsaBal2 = uf (foldr (/=) False)
-- Example 1 from https://ajc.maths.uq.edu.au/pdf/29/ajc_v29_p231.pdf
-- n=6; output in hex 04511b5e37e23e6d
deutschJozsaBal3 = uf f
  where shex = "04511b5e37e23e6d"
        h2Int :: Char -> Int
        h2Int c = fst (head (readHex [c]))
        h2Str :: Char -> String
        h2Str c = printf "%04b" (h2Int c)
        sbin :: [Bool]
        sbin = map (== '0') $ concatMap h2Str shex
        f xs = sbin !! fromInteger (toInt xs)

retroDeutschJozsa :: (Show f, Value f) =>
                     FormulaRepr f r -> r -> Int -> ([Bool] -> [Bool]) -> IO ()
retroDeutschJozsa fr base n f = print $ runST $ do
  xs <- newVars (fromVars fr n base)
  y <- newVar zero
  run Circuit { op = synthesis (n+1) (xs ++ [y]) f
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

-- Bernstein-Vazirani
-- n=8, hidden=92 [00111010]

retroBernsteinVazirani fr = print $ runST $ do
  xs <- newVars (fromVars fr 8 "x")
  y <- newVar zero
  let op = fromList [ cx (xs !! 1) y
                    , cx (xs !! 3) y
                    , cx (xs !! 4) y
                    , cx (xs !! 5) y
                    ]
  run Circuit { op = op
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

-- Simon
-- n=2, a=3

retroSimon fr = print $ runST $ do
  xs <- newVars (fromVars fr 2 "x")
  as <- newVars (fromInt 2 0)
  let op = fromList [ cx (head xs) (head as)
                    , cx (head xs) (as !! 1)
                    , cx (xs !! 1) (head as)
                    , cx (xs !! 1) (as !! 1)
                    ]
  run Circuit { op = op
              , xs = xs
              , ancillaIns = as
              , ancillaOuts = as
              , ancillaVals = undefined
              }
  mapM readSTRef as

-- Grover

retroGrover :: (Show f, Value f) =>
               FormulaRepr f r -> r -> Int -> Integer -> IO ()
retroGrover fr base n w = print $ runST $ do
  xs <- newVars (fromVars fr n base)
  y <- newVar zero
  run Circuit { op = synthesis (n+1) (xs ++ [y]) (groverOracle n w)
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y
  where
    groverOracle n w = uf (== xw) where xw = fromInt n w

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
