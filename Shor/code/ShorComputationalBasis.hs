{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module ShorComputationalBasis where

import Prelude hiding (seq)

import Data.Maybe (catMaybes, maybe, fromMaybe, fromJust)
import Data.List (find,union,intersperse,delete,(\\),intersect)

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
-- Circuits are sequences of generalized Toffoli gates manipulating
-- locations holding static boolean values or dynamic values

--
-- Values with either static or dynamic information
-- ------------------------------------------------

type Literal = (Bool,String)

data Formula = Static Bool
             | Symbolic Literal
             | And Formula Formula
             | Or Formula Formula
             | Xor Formula Formula
             | XorList [Literal]
             | Eq Formula Formula
  deriving (Eq,Ord)

isStatic :: Formula -> Bool
isStatic (Static _) = True
isStatic _  = False

isSymbolic :: Formula -> Bool
isSymbolic (Symbolic _) = True
isSymbolic _ = False

extractBool :: Formula -> Bool
extractBool (Static b) = b
extractBool _ = error "Internal error: expecting a static value"

bigFormula :: Formula -> Bool
bigFormula (Static _) = False
bigFormula (Symbolic _) = False
bigFormula (And (Symbolic _) (Symbolic _)) = False
bigFormula (Or (Symbolic _) (Symbolic _)) = False
bigFormula (Xor (Symbolic _) (Symbolic _)) = False
bigFormula (XorList vs) = length vs <= 3
bigFormula (Eq (Symbolic _) (Symbolic _)) = False
bigFormula _ = True

instance Show Formula where
  show (Static b)       = if b then "1" else "0"
  show (Symbolic (b,s)) = if b then s else ("-" ++ s)
  show (And v1 v2)  = printf "(%s . %s)" (show v1) (show v2)
  show (Or  v1 v2)  = printf "(%s + %s)" (show v1) (show v2)
  show (Xor v1 v2)  = printf "(%s # %s)" (show v1) (show v2)
  show (XorList lits)  = printf "(# [%s])"
    (concat (intersperse "," (map (\(b,s) -> if b then s else ("-" ++ s)) lits)))
  show (Eq v1 v2)   = printf "(%s = %s)" (show v1) (show v2)

-- Smart constructors

snot :: Formula -> Formula 
snot (Static b) = Static (not b)
snot (Symbolic (b,s)) = Symbolic (not b, s)
snot (And v1 v2) = sor (snot v1) (snot v2)
snot (Or  v1 v2) = sand (snot v1) (snot v2)
snot (Xor v1 v2) = seq v1 v2
snot (XorList []) = Static True
snot (XorList ((b,s):lits)) = XorList ((not b,s) : lits)
snot (Eq v1 v2) = sxor v1 v2

sand :: Formula -> Formula -> Formula
sand (Static False) v = Static False
sand v (Static False) = Static False
sand (Static True) v = v
sand v (Static True) = v
sand (Symbolic (b1,s1)) (Symbolic (b2,s2)) | s1 == s2 =
  if b1 == b2 then Symbolic (b1,s1) else Static False
sand v1 v2 | v1 /= v2 = v1
sand v1 v2 = And v1 v2

sor :: Formula -> Formula -> Formula
sor (Static False) v = v
sor v (Static False) = v
sor (Static True) v = Static True
sor v (Static True) = Static True
sor (Symbolic (b1,s1)) (Symbolic (b2,s2)) | s1 == s2 =
  if b1 == b2 then Symbolic (b1,s1) else Static True
sor v1 v2 = Or v1 v2

sxor :: Formula -> Formula -> Formula
sxor (Static False) v = v
sxor v (Static False) = v
sxor (Static True) v = snot v
sxor v (Static True) = snot v
sxor (Symbolic (b1,s1)) (Symbolic (b2,s2))
  | s1 == s2 = Static (b1 /= b2)
  | otherwise = XorList [(b1,s1),(b2,s2)]
sxor (Symbolic (b1,s1)) (Xor (Symbolic (b2,s2)) v) 
  | s1 == s2 = if b1 == b2 then v else snot v
  | otherwise = sxor (XorList [(b1,s1),(b2,s2)]) v
sxor (Symbolic (b,s)) (XorList vs) 
  | (b,s) `elem` vs = XorList (delete (not b,s) vs)
  | (not b,s) `elem` vs = snot (XorList (delete (not b,s) vs))
  | otherwise = XorList ((b,s) : vs)
sxor (XorList vs) (Symbolic (b,s))
  | (b,s) `elem` vs = XorList (delete (not b,s) vs)
  | (not b,s) `elem` vs = snot (XorList (delete (not b,s) vs))
  | otherwise = XorList ((b,s) : vs)
sxor (XorList vs) (Xor (Symbolic (b,s)) v)
  | (b,s) `elem` vs = sxor (XorList (delete (not b,s) vs)) v
  | (not b,s) `elem` vs = sxor (snot (XorList (delete (not b,s) vs))) v
  | otherwise = sxor (XorList ((b,s) : vs)) v
{--sxor (XorList vs1) (XorList vs2) =
  let common = intersect vs1 vs2
  in if odd (length common) then snot (XorList ((vs1 ++ vs2) \\ common))
     else XorList ((vs1 ++ vs2) \\ common)
--}
sxor v1 v2 = Xor v1 v2

seq :: Formula -> Formula -> Formula
seq (Static False) v = snot v
seq v (Static False) = snot v
seq (Static True) v = v
seq v (Static True) = v
seq (Symbolic (b1,s1)) (Symbolic (b2,s2)) | s1 == s2 = Static (b1 == b2)
seq v1 v2 = Eq v1 v2

-- More aggressive simplification
-- Be careful: only use with limited depth or limited number of variables

type Env = [(String,Bool)]

makeEnv :: [String] -> [Env]
makeEnv = env
  where baseEnv :: String -> Env
        baseEnv s = [ (s,b) | b <- [False, True] ]

        env :: [String] -> [Env]
        env [] = [[]]
        env (s:ss) = [ t:ts | t <- baseEnv s, ts <- env ss ]

eval :: Formula -> Env -> Bool
eval (Static b) env = b
eval (Symbolic (b,s)) env = (not b) /= (fromJust $ lookup s env)
eval (And v1 v2) env = eval v1 env && eval v2 env
eval (Or v1 v2) env = eval v1 env || eval v2 env
eval (Xor v1 v2) env = eval v1 env /= eval v2 env
eval (XorList []) env = False
eval (XorList (v:vs)) env =
  let vvs = eval (XorList vs) env
  in if eval (Symbolic v) env then not vvs else vvs
eval (Eq v1 v2) env  = eval v1 env == eval v2 env

formulaTT :: Formula -> [String] -> [(Env,Bool)]
formulaTT v vars = [ (env, eval v env) | env <- makeEnv vars ]

generateStatics :: [Formula]
generateStatics = [Static False, Static True]

generateLits :: [String] -> [Formula]
generateLits vars = concatMap (\s -> [Symbolic (False,s), Symbolic (True,s)]) vars

generateOps :: (Formula -> Formula -> Formula) -> [Formula] -> [Formula]
generateOps op fs = [ op f1 f2 | f1 <- fs, f2 <- fs, f1 < f2]

generateFormulas :: Int -> [String] -> [Formula]
generateFormulas 0 vars = generateStatics
generateFormulas 1 vars = generateStatics ++ generateLits vars
generateFormulas depth vars = foldr union [] $ 
  [fs, generateOps sand fs, generateOps sor fs,
   generateOps sxor fs, generateOps seq fs]
  where fs = generateFormulas (depth-1) vars

simplifyForm :: Formula -> Maybe Formula
simplifyForm form | length vars > 5 = Nothing
              | otherwise = do 
  let formTT = formulaTT form vars
  let depth = 2
  let allFormulas = generateFormulas depth vars
  let allTT  = map (\f -> (f, formulaTT f vars)) allFormulas
  (sf,_) <- find (\ (f,ftt) -> formTT == ftt) allTT
  return sf

  where

    vars = extractVars form
    
    extractVars :: Formula -> [String]
    extractVars (Static _) = []
    extractVars (Symbolic (b,s)) = [s]
    extractVars (And v1 v2) = union (extractVars v1) (extractVars v2)
    extractVars (Or v1 v2) = union (extractVars v1) (extractVars v2)
    extractVars (Xor v1 v2) = union (extractVars v1) (extractVars v2)
    extractVars (XorList vs) = map snd vs
    extractVars (Eq v1 v2) = union (extractVars v1) (extractVars v2)

simplifyXor :: Formula  -> Formula -> Maybe Formula
simplifyXor cf tf = simplifyForm (sxor cf tf)

--

data Value = Value { _current :: Formula, _saved :: Maybe Bool }
  deriving Eq

makeLenses ''Value

instance Show Value where
  show v = show (v^.current)

vnot :: Value -> Value
vnot v = set current (snot (v^.current)) v

--

newDynValue :: String -> Value
newDynValue s = Value { _current = Symbolic (True,s), _saved = Nothing }

valueToInt :: [Value] -> Integer
valueToInt = toInt . map (\v -> extractBool (v^.current)) 

--
-- Locations where values are stored
-- ---------------------------------

type Var s = STRef s Value

-- Stateful functions to deal with variables

newVar :: Bool -> ST s (Var s)
newVar b = newSTRef (Value { _current = Static b, _saved = Nothing })

newVars :: [Bool] -> ST s [Var s]
newVars = mapM newVar

newDynVar :: STRef s Int -> String -> ST s (Var s)
newDynVar gensym s = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newDynValue (s ++ show k))

newDynVars :: STRef s Int -> String -> Int -> ST s [Var s]
newDynVars gensym s n = replicateM n (newDynVar gensym s)


-- Generalized Toffoli gates
-- -------------------------

data GToffoli s = GToffoli String [Bool] [Var s] (Var s)
  deriving Eq

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli ctx bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "[%s] GToffoli %s %s (%s)"
    ctx
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

makeAdder :: Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder n as bs = do
  cs <- newVars (fromInt n 0)
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
  ms <- newVars (fromInt (n+1) m)
  ms' <- newVars (fromInt (n+1) m)
  t <- newVar False
  adderab <- makeAdder n as bs
  addermb <- makeAdder n ms bs
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
  ps <- newVars (fromInt (n+1) 0)
  as <- mapM
          (\a -> newVars (fromInt (n+1) a))
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
     | doubleNegs (zip bs (map (^.current) cs)) -> Just False
     | otherwise -> Just True
  where
    r' = and (catMaybes r)

    r = zipWith f bs (map (^.current) cs)

    f b (Static b') = Just (b == b')
    f b _ = Nothing

    doubleNegs [] = False
    doubleNegs ((b, Static b') : bfs) = doubleNegs bfs
    doubleNegs ((b,f) : bfs) = (b, snot f) `elem` bfs || doubleNegs bfs

interpGT :: GToffoli s -> ST s ()
interpGT (GToffoli ctx bs cs t) = do
  controls <- mapM readSTRef cs
  tv <- readSTRef t
  when (controlsActive bs controls == Just True) $ writeSTRef t (vnot tv)

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
                   , _ts    :: [Var s] 
                   , _us   :: [Var s]
                   , _circ  :: OP s
                   }

makeLenses ''InvExpModCircuit

----------------------------------------------------------------------------------------
-- Partial evaluation

restoreSaved :: GToffoli s -> ST s (GToffoli s)
restoreSaved g@(GToffoli ctx bsOrig csOrig t) = do
  vt <- readSTRef t
  maybe
    (return ()) 
    (\vs -> writeSTRef t (set saved Nothing $ set current (Static vs) vt))
    (vt^.saved)
  return g

shrinkControls :: [Bool] -> [Var s] -> [Value] -> ([Bool],[Var s],[Value])
shrinkControls [] [] [] = ([],[],[])
shrinkControls (b:bs) (c:cs) (v:vs)
  | isStatic (v^.current) && extractBool (v^.current) == b = shrinkControls bs cs vs
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
           (set current (Symbolic (False,"_")) $
             set saved (Just $ extractBool (vt^.current)) vt)
         return $ S.singleton (GToffoli ctx bs cs t)

simplifyOP :: OP s -> ST s (OP s)
simplifyOP op = do
  op <- foldMap simplifyG op
  mapM restoreSaved op

simplifyCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
simplifyCircuit c = do
  simplified <- simplifyOP $ c^.circ
  return (set circ simplified c)


-- Generate constraints
-- --------------------

specialCases :: String -> [Bool] -> [Var s] -> Var s -> [Value] -> Value -> ST s ()
specialCases msg [b] [cx] tx [x] y =
  let fc = if b then x^.current else snot (x^.current)
      fs = fromMaybe (sxor fc (y^.current)) (simplifyXor fc (y^.current))
  in  do when (bigFormula fs) $ traceM (printf "%s ==> %s" msg (show fs))
         writeSTRef tx $ set current fs y
specialCases msg [b1,b2] [cx1,cx2] tx [x1,x2] y = 
  let cfr = sand
            (if b1 then x1^.current else snot (x1^.current))
            (if b2 then x2^.current else snot (x2^.current))
      cfs = fromMaybe cfr (simplifyForm cfr)
      tfs = fromMaybe (sxor cfs (y^.current)) (simplifyXor cfs (y^.current))
  in do when (bigFormula tfs) $ traceM (printf "%s ==> %s" msg (show tfs))
        writeSTRef tx $ set current tfs y
specialCases msg bs cs t controls vt = do
  error (printf "Toffoli 4 or more: %s" msg)

peG :: Int -> (GToffoli s, Int) -> ST s (OP s)
peG size (g@(GToffoli ctx bs' cs' t), count) = do
  d <- showGToffoli g
  controls' <- mapM readSTRef cs'
  tv <- readSTRef t
  let (bs,cs,controls) = shrinkControls bs' cs' controls'
  let ca = controlsActive bs controls
  if | ca == Just True -> do
         writeSTRef t (vnot tv)
         return S.empty
     | ca == Just False -> do
         return S.empty
     | otherwise -> do
         specialCases (msg d) bs cs t controls tv
         return (S.singleton (GToffoli ctx bs cs t))

  where msg :: String -> String
        msg d = printf "\nProcessing gate %d of %d:\n\n\t%s" count size d

peCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
peCircuit c = do
  let size = S.length (c^.circ)
  traceM (printf "Original size = %d" size)
  c <- simplifyCircuit c
  let size = S.length (c^.circ)
  op' <- foldMap (peG size) $ S.zip (c^.circ) (S.fromFunction size (+1))
  return $ set circ op' c

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- InvExpMod 

makeInvExpMod :: Int -> Integer -> Integer -> Integer -> ST s (InvExpModCircuit s)
makeInvExpMod n a m res = do
  gensym <- newSTRef 0
  (xs,ts,us) <- if even n
                then do xs <- newDynVars gensym "x" (n+1)
                        ts <- newVars (fromInt (n+1) res)
                        us <- newVars (fromInt (n+1) 0)
                        return (xs,ts,us)
                else do xs <- newDynVars gensym "x" (n+1)
                        ts <- newVars (fromInt (n+1) 0)
                        us <- newVars (fromInt (n+1) res)
                        return (xs,ts,us)
  circuit <- makeExpMod n a m xs ts us
  return (InvExpModCircuit
          { _ps   = Params { numberOfBits = n
                           , base         = a
                           , toFactor     = m
                           }
          , _xs  = xs
          , _ts  = ts
          , _us  = us
          , _circ = S.reverse circuit
          })

runPE :: Int -> Integer -> Integer -> Integer -> IO ()
runPE n a m res = pretty $ runST $ do
  circuit <- makeInvExpMod n a m res 
  circuit <- peCircuit circuit
  xs <- mapM readSTRef (circuit^.xs)
  ts <- mapM readSTRef (circuit^.ts)
  us <- mapM readSTRef (circuit^.us)
  assertMessage "runPE"
    (printf "xs are not symbolic !?: %s" (show xs))
    (assert (all (\x -> isSymbolic (x^.current)) xs))
    (return ())
  return (filter filterStatic $ zip ts (fromInt (n+1) 1),
          filter filterStatic $ zip us (fromInt (n+1) 0))
  where
    filterStatic :: (Value,Bool) -> Bool
    filterStatic (Value {_current = Static b1}, b2) = b1 /= b2
    filterStatic _ = True

    pretty (ts,us) = do
      unless (null ts) (mapM_ print ts)
      unless (null us) (mapM_ print us)

factor :: Integer -> IO ()
factor m = do

  -- The period might be close to m/2 and we need at least m different
  -- values of x that have the same image. We might be able to use
  -- fewer bits but for now we will use log(m^2) bits

      let n = ceiling $ logBase 2 (fromInteger m * fromInteger m)
      a <- randomRIO (2,m-1)
      if gcd m a /= 1 
        then factor m -- lucky guess but try again to test circuit approach
        else do
          x <- randomRIO (0,m)
          let res = powModInteger a x m
          putStr "Running InvExpMod circuit symbolically with: "
          putStrLn (printf "n = %d; a = %d; m = %d; res = %d"
                    n a m res)
          runPE n a m res

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

