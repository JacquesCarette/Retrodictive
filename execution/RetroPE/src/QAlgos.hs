{-# LANGUAGE ViewPatterns #-}

module QAlgos where

import Data.STRef (readSTRef,writeSTRef)
import Data.List (intercalate,group,sort,sortBy)
import Data.Sequence (fromList,Seq)
import qualified Data.Sequence as S (reverse)
import qualified Data.MultiSet as MS

import Control.Monad.ST -- (runST,ST)
import Control.Monad.IO.Class (MonadIO)

import System.Random.Stateful (uniformRM, newIOGenM, mkStdGen, getStdGen, newAtomicGenM, globalStdGen, applyAtomicGen, AtomicGenM, StdGen)
import System.TimeIt

import Numeric (readHex)
import GHC.Show (intToDigit)
import Text.Printf (printf)

import Value (Value(..), fromInt)
import Variable (Var, newVar, newVars)
import GToffoli (cx, ccx, cncx)
import Circuits (Circuit(..), OP)
import Printing.Circuits (showSizes, sizeOP)
import ArithCirc (expm)
import qualified EvalZ (interp,ZValue(..))
import PE (run)
import qualified PEO (run) -- for Grover
import Synthesis (viewL,synthesis,synthesisGrover)
import BoolUtils (toInt)
import FormulaRepr (FormulaRepr(..))
import qualified FormAsLists as FL
import qualified FormAsBitmaps as FB
-- import qualified FormAsMaps  as FM

------------------------------------------------------------------------------
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
mkGen (Just seed) = newAtomicGenM (mkStdGen seed)

-- Generic quantum oracle construction

uf :: ([Bool] -> Bool) -> ([Bool] -> [Bool])
uf f (viewL -> (xs,y)) = xs ++ [f xs /= y]

----------------------------------------------------------------------------------------
-- Quantum algorithms

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

runRetroDeutsch = retroDeutsch FL.formRepr "x"

------------------------------------------------------------------------------
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
  let circ = synthesis (n+1) (xs ++ [y]) f
  run Circuit { op = circ
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

runRetroDeutschJozsa :: Int -> ([Bool] -> [Bool]) -> IO ()
runRetroDeutschJozsa = retroDeutschJozsa FL.formRepr "x"


------------------------------------------------------------------------------
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

runRetroBernsteinVazirani :: IO ()
runRetroBernsteinVazirani = retroBernsteinVazirani FL.formRepr

------------------------------------------------------------------------------
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

runRetroSimon :: IO ()
runRetroSimon = retroSimon FL.formRepr

------------------------------------------------------------------------------
-- Grover

groverCircuit :: Value f =>
  FormulaRepr f r -> r -> Int -> Integer -> ST s (Circuit s f)
groverCircuit fr base n w = do
  xs <- newVars (fromVars fr n base)
  y <- newVar zero
  return $ 
   Circuit { op = synthesisGrover (n+1) (xs ++ [y]) w
           , xs = xs
           , ancillaIns = [y]
           , ancillaOuts = [y]
           , ancillaVals = undefined
           }

retroGrover :: (Show f, Value f) =>
  FormulaRepr f r -> r -> Int -> Integer -> ST a f
retroGrover fr base n w = do
  circ <- groverCircuit fr base n w
  run circ
  readSTRef (head (ancillaIns circ))

runRetroGrover :: Int -> Integer -> IO ()
runRetroGrover n w = do
  let c = runST (retroGrover FB.formRepr 0 n w)
  let d = MS.findMin $ FB.ands c
  print d

retroGrover' :: FormulaRepr FB.Formula r -> r -> Int -> Integer -> ST a FB.Formula 
retroGrover' fr base n w = do
  circ <- groverCircuit fr base n w
  PEO.run circ
  readSTRef (head (ancillaIns circ))

runRetroGrover' :: Int -> Integer -> IO ()
runRetroGrover' n w = do
  let c = runST (retroGrover' FB.formRepr 0 n w)
  let d = MS.findMin $ FB.ands c
  print d

predictGrover :: (Show f, Value f) =>
  FormulaRepr f r -> r -> Int -> Integer -> IO ()
predictGrover fr base n w = print $ runST $ do
  circ <- groverCircuit fr base n w
  run circ { op = S.reverse (op circ) } -- reverse twice
  readSTRef (head (ancillaIns circ))

runGrover :: Int -> Integer -> IO ()
runGrover = predictGrover FB.formRepr 0

--

timeRetroGrover :: Int -> Integer -> IO ()
timeRetroGrover n w = do
  circ <- stToIO (groverCircuit FB.formRepr 0 n w)
  let bigN = toInteger $ 2^n
  (time,form) <- timeItT (stToIO (do run circ
                                     readSTRef (head (ancillaIns circ))))
  printf "Grover: N=%d,\tu=%d;\tformula is %s; time = %.2f seconds\n"
    bigN w (head (words (show form))) time
    
timings :: [Int] -> IO ()
timings = mapM_ (\n -> timeRetroGrover n (2 ^ n - 1))

------------------------------------------------------------------------------
-- Small manually optimized Shor 21 from the IBM paper

shor21 :: Var s v -> Var s v -> Var s v -> Var s v -> Var s v -> OP s v
shor21 c0 c1 c2 q0 q1 = fromList
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

retroShor21 :: (Show f, Value f) =>
               FormulaRepr f r -> r -> Integer -> IO ()
retroShor21 fr base w = print $ runST $ do
  cs <- newVars (fromVars fr 3 base)
  qs <- newVars (fromInt 2 w)
  run Circuit { op = shor21 (cs !! 0) (cs !! 1) (cs !! 2) (qs !! 0) (qs !! 1)
              , xs = cs
              , ancillaIns = qs
              , ancillaOuts = qs
              , ancillaVals = undefined
              }
  mapM readSTRef qs

runShor21 :: Integer -> Integer -> Integer
runShor21 c w = runST $ do
  cs <- newVars (fromInt 3 c)
  qs <- newVars (fromInt 2 w)
  EvalZ.interp (shor21 (cs !! 0) (cs !! 1) (cs !! 2) (qs !! 0) (qs !! 1))
  q <-  mapM readSTRef qs
  return (toInt (map (\(EvalZ.ZValue b) -> b) q))

-- observed input is 2 bits

runRetroShor21 :: Integer -> IO ()
runRetroShor21 = retroShor21 FL.formRepr "x"

------------------------------------------------------------------------------
-- Shor

-- expMod circuit a^x `mod` m
-- r is observed result 

expModCircuit :: (Show f, Value f) =>
            FormulaRepr f r -> r -> Int -> Integer -> Integer -> Integer -> 
            ST s ([(f,f)], [(Int,Int)])
expModCircuit fr base n a m r = do
  circ <- expm n a m
  mapM_ (uncurry writeSTRef) (zip (xs circ) (fromVars fr (n+1) base))
  mapM_ (uncurry writeSTRef) (zip (ancillaOuts circ) (fromInt (n+1) r))
  run circ
  result <- mapM readSTRef (ancillaIns circ)
  let eqs = zip result (ancillaVals circ)
  return (eqs, sizeOP $ op circ)

-- can choose seed or let system choose
-- can choose 'a' or let system choose
-- can choose observed result or use 1

retroShor :: (Show f, Value f) => FormulaRepr f r -> r ->
             Maybe Int -> Maybe Integer -> Maybe Integer -> Integer -> IO ()
retroShor fr base seed maybea mayber m = do
      gen <- mkGen seed
      a <- case maybea of
             Nothing -> uniformRM (2,m-1) gen
             Just a' -> return a'
      let n = ceiling $ logBase 2 (fromInteger m * fromInteger m)
      let r = case mayber of
                Nothing -> 1
                Just r' -> r'
      let gma = gcd m a 
      if gma /= 1 
        then putStrLn (printf "Lucky guess %d = %d * %d\n" m gma (m `div` gma))
        else do putStrLn (printf "n=%d; a=%d\n" n a)
                let res = runST $ expModCircuit fr base n a m r
                printResult res

-- seed a r m

runRetroShor :: Maybe Int -> Maybe Integer -> Maybe Integer -> Integer -> IO ()
runRetroShor = retroShor FB.formRepr 0

----------------------------------------------------------------------------------------
