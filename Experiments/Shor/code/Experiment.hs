{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module Experiment where

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

-- Debug Helpers

debug = True

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
-- Values can static or symbolic formulae
-- Formulae are in "algebraic normal form"

type Literal = String

-- []      = True
-- [a,b,c] = a && b && c

newtype Ands = Ands { lits :: [Literal] }
  deriving (Eq,Ord)

instance Show Ands where
  show as = showL (lits as)
    where showL [] = "1"
          showL ss = concat ss

-- Formula [] = False
-- Formula [[],[a],[b,c]] = True XOR a XOR (b && c)

newtype Formula = Formula { clauses :: [Ands]}
  deriving (Eq,Ord)

instance Show Formula where
  show f = showC (clauses f)
    where
      showC [] = "0"
      showC cs = concat $ intersperse " + " (map show cs)

false :: Formula
false = Formula { clauses = [] }

true :: Formula
true = Formula { clauses = [ Ands [] ] }

isStatic :: Formula -> Bool
isStatic f = f == false || f == true

fromBool :: Bool -> Formula
fromBool False = false
fromBool True = true

toBool :: Formula -> Bool
toBool f | f == false = False
         | f == true = True
         | otherwise = error "Internal error: converting a complex formula to bool"

fromVar :: String -> Formula
fromVar s = Formula { clauses = [ Ands [s] ] }

-- 

simplifyLits :: [Literal] -> [Literal]
simplifyLits [] = []
simplifyLits [s] = [s]
simplifyLits (s1 : s2 : ss) 
  | s1 == s2 = simplifyLits (s2 : ss)
  | otherwise = s1 : simplifyLits (s2 : ss)

simplifyAnds :: [Ands] -> [Ands]
simplifyAnds [] = []
simplifyAnds [c] = [c]
simplifyAnds (c1 : c2 : cs) 
  | c1 == c2 = simplifyAnds cs
  | otherwise = c1 : simplifyAnds (c2 : cs)

snot :: Formula -> Formula
snot f = Formula (simplifyAnds (clauses true ++ clauses f))

sxor :: Formula -> Formula -> Formula
sxor (Formula cs1) (Formula cs2) = Formula (simplifyAnds (sort (cs1 ++ cs2)))

sand :: Formula -> Formula -> Formula
sand (Formula cs1) (Formula cs2) = Formula (simplifyAnds (sort (prod cs1 cs2)))
  where prod cs1 cs2 = [ Ands (simplifyLits (sort (lits c1 ++ lits c2)))
                       | c1 <- cs1, c2 <- cs2 ]
          
--

data Value = Value { _name :: String
                   , _suffix :: String
                   , _current :: Formula
                   , _saved :: Maybe Bool
                   }
  deriving Eq

makeLenses ''Value

instance Show Value where
  show v = show (v^.current)

vnot :: Value -> Value
vnot v = set current (snot (v^.current)) v

--

newValue :: String -> String -> Bool -> Value
newValue name suffix b = Value { _name = name,
                                 _suffix = suffix,
                                 _current = fromBool b ,
                                 _saved = Nothing
                               }

newDynValue :: String -> String -> String -> Value
newDynValue name suffix s = Value { _name = name,
                                    _suffix = suffix,
                                    _current = fromVar s ,
                                    _saved = Nothing
                                  }

valueToInt :: [Value] -> Integer
valueToInt = toInt . map (\v -> toBool (v^.current)) 

----------------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

--
-- Locations where values are stored
-- ---------------------------------<

type Var s = STRef s Value

-- Stateful functions to deal with variables

newVar :: String -> String -> Bool -> ST s (Var s)
newVar name suffix b = newSTRef (newValue name suffix b)

newVars :: String -> Int -> [Bool] -> ST s [Var s]
newVars name zero bs = mapM (\ (b,suffix) -> newVar name (show suffix) b) (zip bs [zero..])

newDynVar :: STRef s Int -> String -> ST s (Var s)
newDynVar gensym s = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newDynValue s (show k) (s ++ show k))

newDynVars :: STRef s Int -> String -> Int -> ST s [Var s]
newDynVars gensym s n = replicateM n (newDynVar gensym s)

--
-- A circuit is a sequence of generalized Toffoli gates
-- ----------------------------------------------------

type OP s = Seq (GToffoli s)

data GToffoli s = GToffoli String [Bool] [Var s] (Var s)
  deriving Eq

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli ctx [] [] t) = do
  vt <- readSTRef t
  return $ printf "x %s[%s];\n" -- \t\t\t%s\n"
    (vt^.name) (vt^.suffix) -- (show (vt^.current))
showGToffoli (GToffoli ctx [b] [c] t) = do
  control <- readSTRef c
  vt <- readSTRef t
  return $ printf "cx %s[%s], %s[%s];\n" -- \t\t\t%s %s\n"
    (control^.name) (control^.suffix)
    (vt^.name) (vt^.suffix) -- (show (control^.current)) (show (vt^.current))
showGToffoli (GToffoli ctx [b1,b2] [c1,c2] t) = do
  [control1,control2] <- mapM readSTRef [c1,c2]
  vt <- readSTRef t
  return $ printf "ccx %s[%s], %s[%s], %s[%s];\n" -- \t\t\t%s %s %s\n"
    (control1^.name) (control1^.suffix)
    (control2^.name) (control2^.suffix)
    (vt^.name) (vt^.suffix) -- (show (control1^.current)) (show (control2^.current)) (show (vt^.current))
showGToffoli (GToffoli ctx [b1,b2,b3] [c1,c2,c3] t) = do
  [control1,control2,control3] <- mapM readSTRef [c1,c2,c3]
  vt <- readSTRef t
  return $ printf "cccx %s[%s], %s[%s], %s[%s], %s[%s];\n"
    (control1^.name) (control1^.suffix)
    (control2^.name) (control2^.suffix)
    (control3^.name) (control3^.suffix)
    (vt^.name) (vt^.suffix)

showOP :: OP s -> ST s String
showOP = foldMap showGToffoli

--
-- Addition, multiplication, and modular exponentiation circuits
-- -------------------------------------------------------------

xop :: String -> Var s -> GToffoli s
xop ctx b = GToffoli ctx [] [] b

cx :: String -> Var s -> Var s -> GToffoli s
cx ctx a b = GToffoli ctx [True] [a] b

ncx :: String -> Var s -> Var s -> GToffoli s
ncx ctx a b = GToffoli ctx [False] [a] b

ccx :: String -> Var s -> Var s -> Var s -> GToffoli s
ccx ctx a b c = GToffoli ctx [True,True] [a,b] c

cop :: String -> Var s -> OP s -> OP s
cop opctx c =
  fmap (\ (GToffoli ctx bs cs t) -> GToffoli (opctx ++ "." ++ ctx) (True:bs) (c:cs) t)

ncop :: String -> Var s -> OP s -> OP s
ncop opctx c =
  fmap (\ (GToffoli ctx bs cs t) -> GToffoli (opctx ++ "." ++ ctx) (False:bs) (c:cs) t)

ccop :: String -> OP s -> [Var s] -> OP s
ccop ctx = foldr (cop ctx)

carryOP :: Var s -> Var s -> Var s -> Var s -> OP s
carryOP c a b c' =
  S.fromList [ccx "carry" a b c', cx "carry" a b, ccx "carry" c b c']

sumOP :: Var s -> Var s -> Var s -> OP s
sumOP c a b =
  S.fromList [cx "sum" a b, cx "sum" c b]

copyOP :: [ Var s ] -> [ Var s ] -> OP s
copyOP as bs = S.fromList (zipWith (cx "copy") as bs)

makeAdder :: Int -> Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder inst n as bs = do
  cs <- newVars "c" inst (fromInt n 0)
  return (loop as bs cs)
    where loop [a,_] [b,b'] [c] =
            (carryOP c a b b') ><
            (singleton (cx "adder" a b)) ><
            (sumOP c a b)
          loop (a:as) (b:bs) (c:c':cs) =
            (carryOP c a b c') ><
            (loop as bs (c':cs)) ><
            (S.reverse (carryOP c a b c')) ><
            (sumOP c a b)

makeAdderMod :: Int -> Integer -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdderMod n m as bs = do
  ms <- newVars "m" 0 (fromInt (n+1) m)
  ms' <- newVars "d" 0 (fromInt (n+1) m)
  t <- newVar "e" "0" False
  adderab <- makeAdder 0 n as bs
  addermb <- makeAdder n n ms bs
  return $
    adderab ><
    S.reverse addermb ><
    singleton (ncx "adderMod" (bs !! n) t) ><
    cop "adderMod" t (copyOP ms' ms) ><
    addermb ><
    cop "adderMod" t (copyOP ms' ms) ><
    S.reverse adderab ><
    singleton (cx "adderMod" (bs !! n) t) ><
    adderab

makeCMulMod :: Int -> Integer -> Integer ->
               Var s -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeCMulMod n a m c xs ts = do
  ps <- newVars "p" 0 (fromInt (n+1) 0)
  as <- mapM
          (\a -> newVars "a" 0 (fromInt (n+1) a))
          (take (n+1) (doublemods a m))
  adderPT <- makeAdderMod n m ps ts
  return (loop adderPT as xs ps)
    where loop adderPT [] [] ps =
            ncop "cMulMod" c (copyOP xs ts) 
          loop adderPT (a:as) (x:xs) ps =
            ccop "cMulMod" (copyOP a ps) [c,x] ><
            adderPT ><
            ccop "cMulMod" (copyOP a ps) [c,x] ><
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

controlsActive :: [Bool] -> [Value] -> Maybe Bool
controlsActive bs cs =
  if | not r' -> Just False
     | Nothing `elem` r -> Nothing
     | otherwise -> Just True
  where
    r' = and (catMaybes r)

    r = zipWith f bs (map (^.current) cs)

    f b form | isStatic form = Just (b == toBool form)
    f b _ = Nothing

interpGT :: GToffoli s -> ST s ()
interpGT (GToffoli ctx bs cs t) = do
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  when (controlsActive bs controls == Just True) $ writeSTRef t (vnot tv)

interpOP :: OP s -> ST s ()
interpOP = foldMap interpGT

----------------------------------------------------------------------------------------
-- Phase to deal with all statically known gates

restoreSaved :: GToffoli s -> ST s (GToffoli s)
restoreSaved g@(GToffoli ctx bsOrig csOrig t) = do
  vt <- readSTRef t
  maybe
    (return ()) 
    (\vs -> writeSTRef t (set saved Nothing $ set current (fromBool vs) vt))
    (vt^.saved)
  return g

shrinkControls :: [Bool] -> [Var s] -> [Value] -> ([Bool],[Var s],[Value])
shrinkControls [] [] [] = ([],[],[])
shrinkControls (b:bs) (c:cs) (v:vs)
  | isStatic (v^.current) && toBool (v^.current) == b = shrinkControls bs cs vs
  | otherwise =
    let (bs',cs',vs') = shrinkControls bs cs vs
    in (b:bs',c:cs',v:vs')

simplifyG :: GToffoli s -> ST s (OP s)
simplifyG (GToffoli ctx bsOrig csOrig t) = do
  controlsOrig <- mapM readSTRef csOrig
  vt <- readSTRef t
  let (bs,cs,controls) = shrinkControls bsOrig csOrig controlsOrig
  let ca = controlsActive bs controls
  if | ca == Just True && isStatic (vt^.current) -> do
         writeSTRef t (vnot vt)
         return S.empty
     | ca == Just False ->
         return S.empty
     | otherwise -> do
         -- save value of target; mark it as unknown for remainder of phase
         when (vt^.saved == Nothing && isStatic (vt^.current)) $
           writeSTRef t
           (set current (fromVar "_") $ 
             set saved (Just $ toBool (vt^.current)) vt)
         return $ S.singleton (GToffoli ctx bs cs t)

simplifyOP :: OP s -> ST s (OP s)
simplifyOP op = do
  op <- foldMap simplifyG op
  mapM restoreSaved op

----------------------------------------------------------------------------------------
-- Phase to run symbolically generating formulae instead of values
-- ---------------------------------------------------------------

specialCases :: String -> [Bool] -> [Var s] -> Var s -> [Value] -> Value -> ST s ()
specialCases msg [b] [cx] tx [x] y =
  let fc = if b then x^.current else snot (x^.current)
      fs = sxor fc (y^.current)
  in  do traceM (printf "%s ==> %s" msg (show fs))
         writeSTRef tx $ set current fs y
specialCases msg [b1,b2] [cx1,cx2] tx [x1,x2] y = 
  let cfs = sand
            (if b1 then x1^.current else snot (x1^.current))
            (if b2 then x2^.current else snot (x2^.current))
      tfs = sxor cfs (y^.current)
  in do traceM (printf "%s ==> %s" msg (show tfs))
        writeSTRef tx $ set current tfs y
specialCases msg bs cs t controls vt = do
  error (printf "%s (Toffoli 4 or more)" msg)

peG :: Int -> (GToffoli s, Int) -> ST s (OP s)
peG size (g@(GToffoli ctx bs' cs' t), count) = do
  controls' <- mapM readSTRef cs'
  tv <- readSTRef t
--  let (bs,cs,controls) = shrinkControls bs' cs' controls'
  let (bs,cs,controls) =  (bs',cs',controls')
  let ca = controlsActive bs controls
  if | ca == Just True -> do
         writeSTRef t (vnot tv)
         return S.empty
     | ca == Just False -> do
         return S.empty
     | otherwise -> do
         let gSimple = GToffoli ctx bs cs t
         d <- showGToffoli gSimple
         let msg = printf "\nProcessing gate %d of %d:\n\n\t%s" count size d
         specialCases msg bs cs t controls tv
         return (S.singleton gSimple)

peOP :: OP s -> ST s (OP s)
peOP op = do
--  op <- simplifyOP op
  let size = S.length op
  foldMap (peG size) $ S.zip op (S.fromFunction size (+1))

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
