{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module ShorWIP where

import Data.Maybe (catMaybes, maybe)
import Data.List (intersperse)

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))

import Control.Lens hiding (op,(:<))
import Control.Monad 
import Control.Monad.ST
import Data.STRef
  
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
-- Circuits are sequences of generalized Toffoli gates manipulating
-- locations holding static boolean values or dynamic values

--
-- Values with either static or dynamic information
-- ------------------------------------------------

data Value = Static Bool
           | Symbolic (Bool,String)
           | And (Bool,String) (Bool,String)
           | Or (Bool,String) (Bool,String)
           | Xor (Bool,String) (Bool,String)
  deriving Eq

instance Show Value where
  show (Static b) = if b then "1" else "0"
  show (Symbolic (b,s)) = if b then s else ("-" ++ s)
  show (And (b1,s1) (b2,s2)) =
    printf "(%s . %s)" (show (Symbolic (b1,s1))) (show (Symbolic (b2,s2)))
  show (Or (b1,s1) (b2,s2)) =
    printf "(%s + %s)" (show (Symbolic (b1,s1))) (show (Symbolic (b2,s2)))
  show (Xor (b1,s1) (b2,s2)) =
    printf "(%s # %s)" (show (Symbolic (b1,s1))) (show (Symbolic (b2,s2)))

-- Symbolic boolean operations when some values are known

negS :: Value -> Value 
negS (Static b) = Static (not b)
negS (Symbolic (b,s)) = Symbolic (not b, s)
negS (And (b1,s1) (b2,s2)) = Or (not b1, s1) (not b2,s2)
negS (Or (b1,s1) (b2,s2)) = And (not b1, s1) (not b2,s2)
negS (Xor (b1,s1) (b2,s2)) = Xor (not b1, s1) (b2,s2)

andS :: Value -> Value -> Either Value String
andS (Static False) v = Left (Static False)
andS v (Static False) = Left (Static False)
andS (Static True) v = Left v
andS v (Static True) = Left v
andS v v' | v == v' = Left v
andS v v' | v == negS v' = Left (Static False)
andS (Symbolic (b1,s1)) (Symbolic (b2,s2)) = Left (And (b1,s1) (b2,s2))
andS (And (b1,s1) (b2,s2)) (Symbolic (b3,s3)) =
  case andS (Symbolic (b1,s1)) (Symbolic (b3,s3)) of
    Left r -> andS r (Symbolic (b2,s2))
    Right s -> Right s
andS (Symbolic (b3,s3)) (And (b1,s1) (b2,s2)) =
  case andS (Symbolic (b1,s1)) (Symbolic (b3,s3)) of
    Left r -> andS r (Symbolic (b2,s2))
    Right s -> Right s
andS (Or (b1,s1) (b2,s2)) (Xor (b3,s3) (b4,s4)) |
  b1 == not b3 && s1 == s3 && b2 == b4 && s2 == s4 =
  Left (And (b1,s1) (b2,s2))
andS v v' = Right (printf "Don't know how to simplify (%s . %s)" (show v) (show v'))

xorS :: Value -> Value -> Either Value String
xorS (Static False) v = Left v
xorS v (Static False) = Left v
xorS (Static True) v = Left (negS v)
xorS v (Static True) = Left (negS v)
xorS v v' | v == v' = Left (Static False)
xorS v v' | v == negS v' = Left (Static True)
xorS (And (b1,s1) (b2,s2)) (Symbolic (b3,s3)) | b1 == b3 && s1 == s3 =
  Left (And (b1,s1) (b2,s2))                                               
xorS (Symbolic (b3,s3)) (And (b1,s1) (b2,s2)) | b1 == b3 && s1 == s3 =
  Left (And (b1,s1) (b2,s2))                                               
xorS (Or (b1,s1) (b2,s2)) (Symbolic (b3,s3)) | b1 == not b3 && s1 == s3 =
  Left (Xor (b3, s3) (b2,s2))
xorS v v' = Right (printf "Don't know how to simplify (%s # %s)" (show v) (show v'))

--

newDynValue :: String -> Value
newDynValue s = Symbolic (True,s)

isStatic :: Value -> Bool
isStatic (Static _) = True
isStatic _ = False

extractBool :: Value -> Bool
extractBool (Static b) = b
extractBool _ = error "Internal error: expecting a static value"

valueToInt :: [Value] -> Integer
valueToInt = toInt . map extractBool

--
-- Locations where values are stored
-- ---------------------------------

type Var s = STRef s Value

-- Stateful functions to deal with variables

newVar :: Bool -> ST s (Var s)
newVar b = newSTRef (Static b)

newVars :: [Bool] -> ST s [Var s]
newVars = mapM newVar

newDynVar :: STRef s Int -> String -> ST s (Var s)
newDynVar gensym s = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newDynValue (s ++ show k))

newDynVars :: STRef s Int -> String -> Int -> ST s [Var s]
newDynVars gensym s n = replicateM n (newDynVar gensym s)

--
-- Generalized Toffoli gates
-- -------------------------

data GToffoli s = GToffoli [Bool] [Var s] (Var s)
  deriving Eq

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
--  return $ printf "GToffoli %-10s%-15s  (%s)\n"
  return $ printf "GToffoli %s %s (%s)"
    (show (map fromEnum bs))
    (show controls)
    (show vt)

--
-- A circuit is a sequence of generalized Toffoli gates
-- ----------------------------------------------------

type OP s = Seq (GToffoli s)

showOP :: OP s -> ST s String
showOP = foldMap showGToffoli

--
-- Addition, multiplication, and modular exponentiation circuits
-- -------------------------------------------------------------

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

-- returns yes/no/unknown as Just True, Just False, Nothing

controlsActive :: [Bool] -> [Value] -> Maybe Bool
controlsActive bs cs =
  if | not r' -> Just False
     | Nothing `elem` r -> Nothing
     | doubleNegs (zip bs cs) -> Just False
     | otherwise -> Just True
  where
    r' = and (catMaybes r)

    r = zipWith f bs cs

    f b (Static b') = Just (b == b')
    f b _ = Nothing

    doubleNegs [] = False
    doubleNegs ((b, Static b') : bvs) = doubleNegs bvs
    doubleNegs ((b,v) : bvs) = (b, negS v) `elem` bvs || doubleNegs bvs

interpGT :: GToffoli s -> ST s ()
interpGT (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  if controlsActive bs controls == Just True 
    then writeSTRef t (negS tv)
    else return ()

interpOP :: OP s -> ST s ()
interpOP = foldMap interpGT

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Setting up for PE

-- Inverse expmod circuits abstraction for PE; can be run with
-- all static parameters or with mixed static and dynamic parameters

data Params =
  Params { numberOfBits :: Int
         , base         :: Integer
         , toFactor     :: Integer
         }

data InvExpModCircuit s =
  InvExpModCircuit { _ps    :: Params
                   , _xs    :: [Var s] 
                   , _rs    :: [Var s] 
                   , _rzs   :: [Var s]
                   , _os    :: [Var s] 
                   , _lzs   :: [Var s]
                   , _circ  :: OP s
                   }

makeLenses ''InvExpModCircuit

----------------------------------------------------------------------------------------
-- Partial evaluation

specialCases :: [Bool] -> [Var s] -> Var s -> [Value] -> Value -> ST s ()
specialCases [b] [cx] tx [x] y = 
  case xorS (if b then x else negS x) y of
    Left v -> do traceM (printf "cx case: simplified target to: %s" (show v))
                 writeSTRef tx v
    Right s -> trace s (error "\n\nCX\n\n")
specialCases [b1,b2] [cx1,cx2] tx [x1,x2] y = do
  case andS (if b1 then x1 else negS x1) (if b2 then x2 else negS x2) of
    Left c -> case xorS c y of 
      Left v ->
        do traceM (printf "ccx case: simplified controls to: %s and target to: %s"
                   (show c) (show v))
           writeSTRef tx v
      Right s -> trace s (error "\n\nCCX control\n\n")
    Right s -> trace s (error "\n\nCCX TODO\n\n")
specialCases bs cs t controls vt = do
  d <- showGToffoli (GToffoli bs cs t)
  trace (printf "Toffoli 4 or more !?") (error "\n\nCCC...X\n\n")

shrinkControls :: [Bool] -> [Var s] -> [Value] -> ([Bool],[Var s],[Value])
shrinkControls [] [] [] = ([],[],[])
shrinkControls (b:bs) (c:cs) (v:vs)
  | isStatic v && extractBool v == b = shrinkControls bs cs vs
  | otherwise =
    let (bs',cs',vs') = shrinkControls bs cs vs
    in (b:bs',c:cs',v:vs')

peG :: Int -> (GToffoli s, Int) -> ST s (OP s)
peG size (g@(GToffoli bs' cs' t), count) = do
  d <- showGToffoli g
  traceM (printf "\nProcessing gate %d of %d: %s" count size d)
  controls' <- mapM readSTRef cs'
  tv <- readSTRef t
  let (bs,cs,controls) = shrinkControls bs' cs' controls'
  let ca = controlsActive bs controls
  if | ca == Just True -> do
         traceM (printf "controls true: execute")
         writeSTRef t (negS tv)
         return S.empty
     | ca == Just False -> do
         traceM (printf "controls false: ignore")
         return S.empty
     | otherwise -> do
         specialCases bs cs t controls tv
         return (S.singleton (GToffoli bs cs t))

peCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
peCircuit c = do
  let size = S.length (c^.circ)
  op' <- foldMap (peG size) $ S.zip (c^.circ) (S.fromFunction size id)
  return $ set circ op' c

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- InvExpMod example

invExpMod15 :: Integer -> ST s (InvExpModCircuit s)
invExpMod15 res = do
  let n = 4
  let a = 7
  let m = 15
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" (n+1)
  ts <- newVars (fromInt (n+1) 0)
  us <- newVars (fromInt (n+1) res)
  circuit <- makeExpMod n a m xs ts us
  return (InvExpModCircuit
          { _ps   = Params { numberOfBits = 4
                           , base         = 7
                           , toFactor     = 15
                           }
          , _xs   = xs
          , _rs   = us
          , _rzs  = ts
          , _os   = ts
          , _lzs  = us
          , _circ = S.reverse circuit
          })

run15PE :: () -> (String,[Value],[(Bool,Value)],[(Bool,Value)])
run15PE () = runST $ do
  circuit <- invExpMod15 13
  circuit <- peCircuit circuit
  tmp <- showOP $ circuit^.circ
  xs <- mapM readSTRef (circuit^.xs)
  os <- mapM readSTRef (circuit^.os)
  lzs <- mapM readSTRef (circuit^.lzs)
  return (tmp, xs, zip (fromInt 5 1) os, zip (fromInt 5 0) lzs)

go :: () -> IO () 
go () = do
  let (tmp,xs,os,lzs) = run15PE ()
  writeFile "tmp.txt" tmp
  putStrLn "xs:"
  mapM_ print xs
  putStrLn "os:"
  mapM_ print os
  putStrLn "lzs:"
  mapM_ print lzs
  
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
