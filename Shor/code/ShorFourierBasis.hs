{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

-- Computational or Z basis
-- Values are sequences of length 1 that takes values False/True
-- Of course we don't actually use sequences of length 1 and just plain booleans
-- Because we want symbolic execution, we have formulae mixing constants with
-- unknowns over these boolean values

-- Running in the computational basis gives us the most significant bit of the
-- period

-- X basis or real wave basis or Fourier 2 basis
-- Values are sequences of length 2 that takes integer values

-- Use comonads to reprsent the "wave"; how each bit contributes to
-- the global correlation?
-- Ideas from cellular automata ??

-- Running in the X basis gives us information about phase difference
-- between values

-- Y basis or Fourier 4 basis should give more information and we
-- can keep going to Fourier 2^n basis

-- So we have particle physics; real waves; complex waves

module ShorFourierBasis where

import Prelude hiding (seq)

import Data.Maybe (catMaybes, maybe, fromMaybe, fromJust)
import Data.List (find,union,intersperse,delete,(\\),intersect,sort,nub)

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))

import Control.Lens hiding (op,(:<))
import Control.Monad 
import Control.Monad.ST
import Data.STRef

import System.Random (randomRIO)
import GHC.Integer.GMP.Internals (powModInteger)
  
import Text.Printf (printf)
import Test.QuickCheck hiding ((><))
import Control.Exception.Assert (assert, assertMessage)
import qualified Debug.Trace as Debug

----------------------------------------------------------------------------------------
-- Simple helpers

debug = False

trace :: String -> a -> a
trace s a = if debug then Debug.trace s a else a

traceM :: Applicative f => String -> f ()
traceM s = if debug then Debug.traceM s else pure ()

-- Numeric computations

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

toInt :: [Bool] -> Integer
toInt bs = foldr (\ b n -> toInteger (fromEnum b) + 2*n) 0 bs

doublemods :: Integer -> Integer -> [Integer]
doublemods a m = a : doublemods ((2*a) `mod` m) m

sqmods :: Integer -> Integer -> [Integer]
sqmods a m = am : sqmods (am * am) m
  where am = a `mod` m

invmod :: Integer -> Integer -> Integer
invmod x m = loop x m 0 1
  where
    loop 0 1 a _ = a `mod` m
    loop 0 _ _ _ = error "Panic: Inputs not coprime"
    loop x b a u = loop (b `mod` x) x u (a - (u * (b `div` x)))

invsqmods :: Integer -> Integer -> [Integer]
invsqmods a m = invam : invsqmods (am * am) m
  where am = a `mod` m
        invam = a `invmod` m 

----------------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

--
-- Locations where values are stored
-- ---------------------------------<

type Var s = STRef s Bool

newVar :: Bool -> ST s (Var s)
newVar = newSTRef 

newVars :: [Bool] -> ST s [Var s]
newVars = mapM newVar

--
-- A circuit is a sequence of generalized Toffoli gates
-- ----------------------------------------------------

data GToffoli s = GToffoli [Bool] [Var s] (Var s)
  deriving Eq

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %s %s (%s)"
    (show (map fromEnum bs))
    (show controls)
    (show vt)

type OP s = Seq (GToffoli s)

showOP :: OP s -> ST s String
showOP = foldMap showGToffoli

--
-- Addition, multiplication, and modular exponentiation circuits
-- -------------------------------------------------------------

xop ::  Var s -> GToffoli s
xop a = GToffoli [] [] a

cx :: Var s -> Var s -> GToffoli s
cx a b = GToffoli [True] [a] b

ncx :: Var s -> Var s -> GToffoli s
ncx a b = GToffoli [False] [a] b

ccx :: Var s -> Var s -> Var s -> GToffoli s
ccx a b c = GToffoli [True,True] [a,b] c

cop :: Var s -> OP s -> OP s
cop c = fmap (\ (GToffoli bs cs t) -> GToffoli (True:bs) (c:cs) t)

ncop :: Var s -> OP s -> OP s
ncop c = fmap (\ (GToffoli bs cs t) -> GToffoli (False:bs) (c:cs) t)
  
ccop :: OP s -> [Var s] -> OP s
ccop = foldr cop

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' = S.fromList [ccx a b c', cx a b, ccx c b c']

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b = S.fromList [cx a b, cx c b]

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = S.fromList (zipWith cx as bs)

makeAdder :: Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder n as bs = do
  cs <- newVars (fromInt n 0)
  return (loop as bs cs)
    where loop [a,_] [b,b'] [c] =
            (carryOP c a b b') ><
            (singleton (cx a b)) ><
            (sumOP c a b)
          loop (a:as) (b:bs) (c:c':cs) =
            (carryOP c a b c') ><
            (loop as bs (c':cs)) ><
            (S.reverse (carryOP c a b c')) ><
            (sumOP c a b)

makeAdderMod :: Int -> Integer -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdderMod n m as bs = do
  ms <- newVars (fromInt (n+1) m)
  ms' <- newVars (fromInt (n+1) m)
  t <- newVar False
  adderab <- makeAdder n as bs
  addermb <- makeAdder n ms bs
  return $
    adderab ><
    S.reverse addermb ><
    singleton (ncx (bs !! n) t) ><
    cop t (copyOP ms' ms) ><
    addermb ><
    cop t (copyOP ms' ms) ><
    S.reverse adderab ><
    singleton (cx (bs !! n) t) ><
    adderab

makeCMulMod :: Int -> Integer -> Integer ->
               Var s -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeCMulMod n a m c xs ts = do
  ps <- newVars (fromInt (n+1) 0)
  as <- mapM
          (\a -> newVars (fromInt (n+1) a))
          (take (n+1) (doublemods a m))
  adderPT <- makeAdderMod n m ps ts
  return (loop adderPT as xs ps)
    where loop adderPT [] [] ps =
            ncop c (copyOP xs ts) 
          loop adderPT (a:as) (x:xs) ps =
            ccop (copyOP a ps) [c,x] ><
            adderPT ><
            ccop (copyOP a ps) [c,x] ><
            loop adderPT as xs ps

-- if n odd, result is in ts
-- if n even, result is in us

makeExpMod :: Int -> Integer -> Integer ->
              [ Var s ] -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeExpMod n a m xs ts us = do
  let sqs = take (n+1) (sqmods a m)
  let invsqs = take (n+1) (invsqmods a m)
  makeStages 0 n sqs invsqs m xs ts us
    where
      makeStages i n [] [] m [] ts us = return S.empty
      makeStages i n (sq:sqs) (invsq:invsqs) m (c:cs) ts us
        | even i = do
            mulsqMod <- makeCMulMod n sq m c ts us
            mulinvsqMod <- makeCMulMod n invsq m c us ts
            rest <- makeStages (i+1) n sqs invsqs m cs ts us
            return (mulsqMod ><
                    S.reverse mulinvsqMod ><
                    rest)
        | otherwise = do
            mulsqMod <- makeCMulMod n sq m c us ts
            mulinvsqMod <- makeCMulMod n invsq m c ts us
            rest <- makeStages (i+1) n sqs invsqs m cs ts us
            return (mulsqMod ><
                    S.reverse mulinvsqMod ><
                    rest)

----------------------------------------------------------------------------------------
-- Standard evaluation

-- checking whether controls are active
-- returns yes/no/unknown as Just True, Just False, Nothing

controlsActive :: [Bool] -> [Bool] -> Bool
controlsActive bs cs = and (zipWith (==) bs cs)

interpGT :: GToffoli s -> ST s ()
interpGT (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  when (controlsActive bs controls) $ writeSTRef t (not tv)

interpOP :: OP s -> ST s ()
interpOP = foldMap interpGT

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Making and executing circuits

data Params =
  Params { numberOfBits :: Int
         , base         :: Integer
         , toFactor     :: Integer
         }

data ExpModCircuit s =
  ExpModCircuit { _ps    :: Params
                , _xs    :: [Var s] 
                , _rs    :: [Var s] 
                , _circ  :: OP s
                }

makeLenses ''ExpModCircuit

makeExpModCircuit :: Int -> Integer -> Integer -> ST s (ExpModCircuit s)
makeExpModCircuit n a m = do
  gensym <- newSTRef 0
  xs <- newVars (fromInt (n+1) 0) -- real input 
  ts <- newVars (fromInt (n+1) 1)
  us <- newVars (fromInt (n+1) 0)
  circuit <- makeExpMod n a m xs ts us
  return (ExpModCircuit
          { _ps   = Params { numberOfBits = n
                           , base         = a
                           , toFactor     = m
                           }
          , _xs  = xs
          , _rs  = if odd n then ts else us
          , _circ = circuit
          })

chooseParams :: Integer -> IO Params
chooseParams m = do
  let n = ceiling $ logBase 2 (fromInteger m * fromInteger m)
  a <- randomRIO (2,m-1)
  if gcd m a /= 1 
    then chooseParams m
    else return (Params { numberOfBits = n, base = a, toFactor = m })

runForward :: Params -> Integer -> Integer 
runForward (Params { numberOfBits = n, base = a, toFactor = m}) x = runST $ do
  circuitR <- makeExpModCircuit n a m
  mapM_ (uncurry writeSTRef) (zip (circuitR^.xs) (fromInt (n+1) x))
  interpOP (circuitR^.circ)
  res <- mapM readSTRef (circuitR^.rs)
  return (toInt res)

goR :: Params -> IO ()
goR p@(Params { numberOfBits = n, base = a, toFactor = m}) = do
    x <- randomRIO (0,m)
    putStr "Running ExpMod circuit with: "
    putStrLn (printf "n = %d; a = %d; m = %d; x = %d" n a m x)
    putStrLn (printf "Result = %d" (runForward p x))

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

