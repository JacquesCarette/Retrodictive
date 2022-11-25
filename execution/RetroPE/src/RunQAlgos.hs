{-# LANGUAGE ViewPatterns #-}

module RunQAlgos where

import Data.STRef (readSTRef,writeSTRef)
import qualified Data.Sequence as S (reverse)
import qualified Data.MultiSet as MS

import Control.Monad.ST -- (runST,ST)

import System.Random.Stateful (uniformRM, mkStdGen, newAtomicGenM, globalStdGen, AtomicGenM, StdGen)
import System.TimeIt

import Text.Printf (printf)

import QAlgos
import Value (Value(..), fromInt)
import Variable (newVar, newVars)
import ArithCirc (expm)
import Circuits (Circuit(..))
import Printing.Circuits (showSizes, sizeOP)
import qualified EvalZ (interp)
import SymbEval (run)
import qualified SymbEvalSpecialized (run) -- for Grover
import BoolUtils (toInt)
import VarInFormula (VarInFormula(..))
import qualified FormAsLists as FL
import qualified FormAsBitmaps as FB

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

----------------------------------------------------------------------------------------
--  Set up the circuits and run them
----------------------------------------------------------------------------------------

retroDeutsch :: (Show f, Value f) => VarInFormula f r -> r -> ([Bool] -> [Bool]) -> IO ()
retroDeutsch fr base f = print $ runST $ do
  x <- newVar (fromVar fr base)
  y <- newVar zero
  run Circuit { op = deutschCircuit f x y
              , xs = [x]
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

runRetroDeutsch :: ([Bool] -> [Bool]) -> IO ()
runRetroDeutsch = retroDeutsch FL.vif "x"

----------------------------------------------------------------------------------------

initDeutschJozsaCircuit :: Value f =>
  VarInFormula f r -> r -> Int -> ([Bool] -> [Bool]) -> ST s (Circuit s f)
initDeutschJozsaCircuit fr base n f = do
  xs <- newVars (fromVars fr n base)
  y <- newVar zero
  let circ = deutschJozsaCircuit n f (xs ++ [y])
  return $ 
      Circuit { op = circ
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }

retroDeutschJozsa :: (Show f, Value f) =>
                     VarInFormula f r -> r -> Int -> ([Bool] -> [Bool]) -> IO ()
retroDeutschJozsa fr base n f = print $ runST $ do
  circ <- initDeutschJozsaCircuit fr base n f
  run circ
  readSTRef (head (ancillaIns circ))

runRetroDeutschJozsa :: Int -> ([Bool] -> [Bool]) -> IO ()
runRetroDeutschJozsa = retroDeutschJozsa FL.vif "x"

timeRetroDJ :: Value f => VarInFormula f r -> r -> Int -> ([Bool] -> [Bool]) -> IO ()
timeRetroDJ fr base n f = do
  circ <- stToIO (initDeutschJozsaCircuit fr base n f)
  let bigN = toInteger $ (2^n :: Integer)
  (time,form) <- timeItT (stToIO (do run circ
                                     readSTRef (head (ancillaIns circ))))
  printf "Deutsch-Jozsa: N=%d,\tformula is = %s; time = %.2f seconds\n"
    bigN (show form) time
    
----------------------------------------------------------------------------------------

retroBernsteinVazirani :: Value a => VarInFormula a [Char] -> IO ()
retroBernsteinVazirani fr = print $ runST $ do
  xs <- newVars (fromVars fr 8 "x")
  y <- newVar zero
  let op = retroBernsteinVaziraniCircuit xs y
  run Circuit { op = op
              , xs = xs
              , ancillaIns = [y]
              , ancillaOuts = [y]
              , ancillaVals = undefined
              }
  readSTRef y

runRetroBernsteinVazirani :: IO ()
runRetroBernsteinVazirani = retroBernsteinVazirani FL.vif

----------------------------------------------------------------------------------------

retroSimon :: Value b => VarInFormula b [Char] -> IO ()
retroSimon fr = print $ runST $ do
  xs <- newVars (fromVars fr 2 "x")
  as <- newVars (fromInt 2 0)
  let op = simonCircuit23 xs as
  run Circuit { op = op
              , xs = xs
              , ancillaIns = as
              , ancillaOuts = as
              , ancillaVals = undefined
              }
  mapM readSTRef as

runRetroSimon :: IO ()
runRetroSimon = retroSimon FL.vif

----------------------------------------------------------------------------------------

runRetroGrover :: Int -> Integer -> IO ()
runRetroGrover n w = do
  let c = runST (retroGrover FB.vif 0 n w)
  let d = MS.findMin $ FB.ands c
  print d

runRetroGrover' :: Int -> Integer -> IO ()
runRetroGrover' n w = do
  let c = runST (retroGrover' FB.vif 0 n w)
  let d = MS.findMin $ FB.ands c
  print d

runGrover :: Int -> Integer -> IO ()
runGrover = predictGrover FB.vif 0

groverCircuit :: Value f =>
  VarInFormula f r -> r -> Int -> Integer -> ST s (Circuit s f)
groverCircuit fr base n w = do
  xs <- newVars (fromVars fr n base)
  y <- newVar zero
  return $! 
   Circuit { op = groverCirc y xs n w
           , xs = xs
           , ancillaIns = [y]
           , ancillaOuts = [y]
           , ancillaVals = undefined
           }

retroGrover :: (Show f, Value f) =>
  VarInFormula f r -> r -> Int -> Integer -> ST a f
retroGrover fr base n w = do
  circ <- groverCircuit fr base n w
  run circ
  readSTRef (head (ancillaIns circ))

retroGrover' :: VarInFormula FB.Formula r -> r -> Int -> Integer -> ST a FB.Formula 
retroGrover' fr base n w = do
  circ <- groverCircuit fr base n w
  SymbEvalSpecialized.run circ
  readSTRef (head (ancillaIns circ))

predictGrover :: (Show f, Value f) =>
  VarInFormula f r -> r -> Int -> Integer -> IO ()
predictGrover fr base n w = print $ runST $ do
  circ <- groverCircuit fr base n w
  run circ { op = S.reverse (op circ) } -- reverse twice
  readSTRef (head (ancillaIns circ))
--

timeRetroGrover :: (Show f, Value f) =>
  VarInFormula f r -> r -> Int -> Integer -> IO ()
timeRetroGrover fr base n w = do
  circ <- stToIO $ groverCircuit fr base n w
  let bigN = toInteger $ (2^n :: Integer)
  (time,form) <- timeItT (stToIO (do run circ
                                     readSTRef (head (ancillaIns circ))))
  printf "Grover: N=%d,\tu=%d;\tformula is %s; time = %f seconds\n"
    bigN w (head (words (show form))) time
    
timeRetroGrover' :: (Show f, Value f) =>
  VarInFormula f r -> r -> Int -> Integer -> f
timeRetroGrover' fr base n w = runST $ do
  circ <- groverCircuit fr base n w
  run circ 
  readSTRef (head (ancillaIns circ))
    
------------------------------------------------------------------------------
-- Shor

-- expMod circuit a^x `mod` m
-- r is observed result 

expModCircuit :: (Show f, Value f) =>
            VarInFormula f r -> r -> Int -> Integer -> Integer -> Integer -> 
            ST s ([(f,f)], [(Int,Int)])
expModCircuit fr base n a m r = do
  circ <- expm n a m
  mapM_ (uncurry writeSTRef) (zip (xs circ) (fromVars fr (n+1) base))
  mapM_ (uncurry writeSTRef) (zip (ancillaOuts circ) (fromInt (n+1) r))
  run circ
  result <- mapM readSTRef (ancillaIns circ)
  let eqs = zip result (ancillaVals circ)
  return (eqs, sizeOP $ op circ)

retroShor21 :: (Show f, Value f) =>
               VarInFormula f r -> r -> Integer -> IO ()
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
  return (toInt q)

-- observed input is 2 bits

runRetroShor21 :: Integer -> IO ()
runRetroShor21 = retroShor21 FL.vif "x"

-- can choose seed or let system choose
-- can choose 'a' or let system choose
-- can choose observed result or use 1

retroShor :: (Show f, Value f) => VarInFormula f r -> r ->
             Maybe Int -> Maybe Integer -> Maybe Integer -> Integer -> IO ()
retroShor fr base seed maybea mayber m = do
      gen <- mkGen seed
      a <- case maybea of
             Nothing -> uniformRM (2,m-1) gen
             Just a' -> return a'
      let n = ceiling $ (logBase 2 (fromInteger m * fromInteger m) :: Double)
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
runRetroShor = retroShor FB.vif 0

