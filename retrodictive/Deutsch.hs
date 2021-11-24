module Deutsch where

import qualified Data.Sequence as S
import Data.Sequence (Seq,singleton,(><))

import Data.STRef

import Control.Monad.ST

import System.Random (randomRIO)

import GHC.Integer.GMP.Internals (powModInteger)

import Text.Printf (printf)

--

import Circuit
import PE
import ANF

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Eventual entry point

data BC = Balanced | Constant
  deriving Show

-- Generally:
-- uf (x,y) = (x, y + f(x))

-- uzero (x,y) = (x, y)

uzero :: Var s -> Var s -> OP s
uzero x y = S.empty

-- uone (x,y) = (x, not y)

uone :: Var s -> Var s -> OP s
uone x y = S.singleton (xop y)

-- uid (x,y) = (x, y + x)

uid :: Var s -> Var s -> OP s
uid x y = S.singleton $ cx "ID" x y

-- unot (x,y) = (x, y + not x)

unot :: Var s -> Var s -> OP s
unot x y = S.singleton (ncx "NOT" x y)

--

deutschArgs =
  [("Constant zero",uzero)
  ,("Constant one", uone)
  ,("Id",uid)
  ,("Not",unot)]

--

deutschST a = runST $ do
  let (name,op) = deutschArgs !! a
  x <- newSTRef (newDynValue "x")
  y <- newSTRef (newValue True) -- newSTRef (newDynValue "y")
  let rop = S.reverse (op x y)
  rop' <- peOP rop
  xv <- readSTRef x
  yv <- readSTRef y
  return (name,xv,yv)

deutsch :: Int -> IO ()
deutsch a = do
--  a <- randomRIO (0,3)
  let (name,xv,yv) = deutschST a
  putStrLn ("Case: " ++ name)
--  printf "xin =  %s\n" (show xv)
  printf "yin =  %s\n" (show yv)

test = do deutsch 0; deutsch 1; deutsch 2; deutsch 3

----------------------------------------------------------------------------------------
-- Deutsch-Jozsa

djzero :: [Var s] -> Var s -> OP s
djzero xs y = S.empty

djone :: [Var s] -> Var s -> OP s
djone xs y = S.singleton (xop y)

djbalanced :: [Var s] -> Var s -> OP s
djbalanced xs y = foldMap (\x -> S.singleton (cx "Balanced" x y)) xs

djST n choose = runST $ do
  let op = case choose of
             0 -> djzero
             1 -> djone
             2 -> djbalanced
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" n
  y <- newSTRef (newValue True) 
  let rop = S.reverse (op xs y)
  rop' <- peOP rop
  xsv <- mapM readSTRef xs
  yv <- readSTRef y
  return (xsv,yv)

dj :: Int -> IO ()
dj n = do 
  let (xsv,yv) = djST n 0
--  mapM_ (\ v -> printf "%s\n" (show v)) xsv
  printf "yin =  %s\n" (show yv)

  let (xsv,yv) = djST n 1
--  mapM_ (\ v -> printf "%s\n" (show v)) xsv
  printf "yin =  %s\n" (show yv)

  let (xsv,yv) = djST n 2
--  mapM_ (\ v -> printf "%s\n" (show v)) xsv
  printf "yin =  %s\n" (show yv)

----------------------------------------------------------------------------------------
-- Grover (sudoku circuit from Qiskit page)

groverOP :: [Var s] -> [Var s] -> Var s -> OP s
groverOP vs cs out =
  S.fromList [
  cx "grover" (vs !! 0) (cs !! 0), 
  cx "grover" (vs !! 1) (cs !! 0), 
  cx "grover" (vs !! 0) (cs !! 1), 
  cx "grover" (vs !! 2) (cs !! 1), 
  cx "grover" (vs !! 1) (cs !! 2), 
  cx "grover" (vs !! 3) (cs !! 2), 
  cx "grover" (vs !! 2) (cs !! 3), 
  cx "grover" (vs !! 3) (cs !! 3),
  GToffoli "grover"
    [True,True,True,True]
    [cs !! 0, cs !! 1, cs !! 2, cs !! 3]
    out,
  cx "grover" (vs !! 0) (cs !! 0), 
  cx "grover" (vs !! 1) (cs !! 0), 
  cx "grover" (vs !! 0) (cs !! 1), 
  cx "grover" (vs !! 2) (cs !! 1), 
  cx "grover" (vs !! 1) (cs !! 2), 
  cx "grover" (vs !! 3) (cs !! 2), 
  cx "grover" (vs !! 2) (cs !! 3), 
  cx "grover" (vs !! 3) (cs !! 3)]
    
groverST = runST $ do
  gensym <- newSTRef 0
  vs <- newDynVars gensym "v" 4
  writeSTRef (vs !! 0) (newValue False)
  writeSTRef (vs !! 3) (newValue False)
  cs <- newVars [False,False,False,False]
  out <- newVar True
  peOP (S.reverse (groverOP vs cs out))
  vvs <- mapM readSTRef vs
  vcs <- mapM readSTRef cs
  vout <- readSTRef out
  return (vvs,vcs,vout)

grover :: IO ()
grover = do
  let (vvs,vcs,vout) = groverST
  mapM_ (\ v -> printf "vs = %s\n" (show v)) vvs
  mapM_ (\ v -> printf "cs = %s\n" (show v)) vcs
  printf "out =  %s\n" (show vout)
  
  -- v0 = 0; v3 = 1 => no solutions
  -- v0 = 0; v3 = 0 => not (v1v2)

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
