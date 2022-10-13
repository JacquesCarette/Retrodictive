module Test.Synthesis where

import Control.Monad.ST (runST)
import Data.STRef (newSTRef)

import Value (Value(..), fromInt)
import Variable (Var, newVar, newVars)
import FormulaRepr (FormulaRepr(..))
import Circuits (showOP)
import Synthesis (synthesis)

----------------------------------------------------------------------------------------
-- Some test cases of the synthesis algorithm

test1 :: IO ()
test1 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  let op = synthesis 2 [x1,x0] (\[a,b] -> [a,a/=b])
  showOP op

test2 :: IO ()
test2 = putStrLn $ runST $ do
  x0 <- newSTRef "x0"
  x1 <- newSTRef "x1"
  x2 <- newSTRef "x2"
  let op = synthesis 3 [x2,x1,x0] (\[a,b,c] -> [a,b,(a&&b)/=c])
  showOP op

test3 :: IO () 
test3 = putStrLn $ runST $ do
  x0 <- newSTRef "x1"
  x1 <- newSTRef "x2"
  x2 <- newSTRef "x3"
  let op = synthesis 3 [x0,x1,x2] f
  showOP op 
  where f [False,False,False] = [True,True,True]     -- 7
        f [False,False,True]  = [False,False,False]  -- 0
        f [False,True,False]  = [True,True,False]    -- 6
        f [False,True,True]   = [True,False,False]   -- 4
        f [True,False,False]  = [False,True,False]   -- 2 
        f [True,False,True]   = [False,False,True]   -- 1
        f [True,True,False]   = [False,True,True]    -- 3
        f [True,True,True]    = [True,False,True]    -- 5

test4 :: Int -> IO ()
test4 n = putStrLn $ runST $ do
  xs <- mapM (newSTRef . (\i -> "[0..(n-1)]" ++ show i)) [0..(n-1)]
  y <- newSTRef "y"
  let op = synthesis (n+1) (xs ++ [y]) id
  showOP op 

----------------------------------------------------------------------------------------
