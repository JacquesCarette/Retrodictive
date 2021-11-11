{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module ShorOptimizedFourierBasis where

import Control.Monad 
import Control.Monad.ST
import Control.Lens hiding (op,(:<))
import Control.Exception.Assert (assert, assertMessage)

import Data.List (nub,intersperse,sort,union,(\\))
import Data.STRef
import qualified Data.Sequence as S
import Data.Sequence (Seq,singleton,(><))
import Data.Maybe (catMaybes)

import System.Random (randomRIO)

import GHC.Integer.GMP.Internals (powModInteger)

import Text.Printf (printf)
import qualified Debug.Trace as D

----------------------------------------------------------------------------------------
-- Insight:
-- If bit j is unknown, then QFT is 0
-- If bit j is known, then QFT gives period 2^(j+1)
-- So we only need to keep track of whether a bit is known or unknown

----------------------------------------------------------------------------------------
-- Debug Helpers

debug = False

trace :: String -> a -> a
trace s a = if debug then D.trace s a else a

traceM :: Applicative f => String -> f ()
traceM s = if debug then D.traceM s else pure ()

----------------------------------------------------------------------------------------
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

-- maintain sorted

newtype Ands = Ands { lits :: [Literal] }
  deriving Eq

instance Show Ands where
  show as = showL (lits as)
    where showL [] = "1"
          showL ss = concat ss

instance Ord Ands where
  (Ands lits1) <= (Ands lits2) =
    length lits1 < length lits2 ||
    (length lits1 == length lits2 && lits1 < lits2)

-- Formula [] = False
-- Formula [[],[a],[b,c]] = True XOR a XOR (b && c)

-- maintain no clause is a subset of another

newtype Formula = Formula { clauses :: [Ands]}
  deriving (Eq,Ord)

instance Show Formula where
  show f = showC (clauses f)
    where
      showC [] = "0"
      showC cs = concat $ intersperse " + " (map show cs)

extractVarsF :: Formula -> [String]
extractVarsF f = foldr union [] (map lits (clauses f))

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

mergeLits :: [Literal] -> [Literal] -> [Literal]
mergeLits [] ss = ss
mergeLits ss [] = ss
mergeLits (s1:ss1) (s2:ss2) | s1 < s2 = s1 : mergeLits ss1 (s2:ss2)
                            | s2 < s1 = s2 : mergeLits (s1:ss1) ss2
                            | otherwise = mergeLits ss1 (s2 : ss2)

-- As far as period funding is concerned
--   a + ab
-- is the same as
--   ab
-- so remove subsets

simplifyAnds :: [Ands] -> [Ands]
simplifyAnds [] = []
simplifyAnds [c] = [c]
simplifyAnds (c1 : c2 : cs) 
  | c1 == c2 = simplifyAnds cs
  | any (\c -> null $ lits c1 \\ lits c) (c2 : cs) = simplifyAnds (c2 : cs)
  | otherwise = c1 : simplifyAnds (c2 : cs)

-- As far as period finding is concerned
--   f
-- is the same as
--   not f

snot :: Formula -> Formula
snot f = f 

sxor :: Formula -> Formula -> Formula
sxor (Formula cs1) (Formula cs2) = Formula (simplifyAnds (sort (cs1 ++ cs2)))

sand :: Formula -> Formula -> Formula
sand (Formula cs1) (Formula cs2) = Formula (simplifyAnds (sort (prod cs1 cs2)))
  where
    prod cs1 cs2 = [ Ands (mergeLits (lits c1) (lits c2)) | c1 <- cs1, c2 <- cs2 ]
          
--

data Value = Value { _current :: Formula, _saved :: Maybe Bool }
  deriving Eq

makeLenses ''Value

instance Show Value where
  show v = show (v^.current)

vnot :: Value -> Value
vnot v = set current (snot (v^.current)) v

--

newValue :: Bool -> Value
newValue b = Value { _current = fromBool b , _saved = Nothing }

newDynValue :: String -> Value
newDynValue s = Value { _current = fromVar s , _saved = Nothing }

valueToInt :: [Value] -> Integer
valueToInt = toInt . map (\v -> toBool (v^.current)) 

----------------------------------------------------------------------------------------
-- Circuits manipulate locations holding values

--
-- Locations where values are stored
-- ---------------------------------<

type Var s = STRef s Value

-- Stateful functions to deal with variables

newVar :: Bool -> ST s (Var s)
newVar = newSTRef . newValue

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
-- A circuit is a sequence of generalized Toffoli gates
-- ----------------------------------------------------

type OP s = Seq (GToffoli s)

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
----------------------------------------------------------------------------------------
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
                   , _us    :: [Var s]
                   , _circ  :: OP s
                   }

makeLenses ''InvExpModCircuit

makeInvExpMod :: Int -> Integer -> Integer -> Integer -> ST s (InvExpModCircuit s)
makeInvExpMod n a m res = do
  gensym <- newSTRef 0
  (xs,ts,us) <- if odd n
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

interpCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
interpCircuit c = do
  interpOP (c^.circ)
  return c

runForward :: Int -> Integer -> Integer -> Integer -> Integer
runForward n a m x = runST $ do
  circuitR <- makeInvExpMod n a m 0
  mapM_ (uncurry writeSTRef) (zip (circuitR^.xs) (map newValue (fromInt (n+1) x)))
  mapM_ (uncurry writeSTRef) (zip (circuitR^.ts) (map newValue (fromInt (n+1) 1)))
  mapM_ (uncurry writeSTRef) (zip (circuitR^.us) (map newValue (fromInt (n+1) 0)))
  let circuit = set circ (S.reverse (circuitR^.circ)) circuitR
  circuit <- interpCircuit circuit
  xs <- mapM readSTRef (circuit^.xs)
  ts <- mapM readSTRef (circuit^.ts)
  us <- mapM readSTRef (circuit^.us)
  let res = if odd n then ts else us
  let zeros = if odd n then us else ts
  assertMessage "runForward"
    (printf "xs have changed to %d" (valueToInt xs))
    (assert (x == valueToInt xs))
    (return ())
  assertMessage "runForward"
    (printf "us are not 0s: %d" (valueToInt zeros))
    (assert (0 == valueToInt zeros))
    (return ())
  return (valueToInt res)

runBackward :: Int -> Integer -> Integer -> Integer -> Integer -> Bool
runBackward n a m x res = runST $ do
  circuit <- makeInvExpMod n a m res
  mapM_ (uncurry writeSTRef) (zip (circuit^.xs) (map newValue (fromInt (n+1) x)))
  circuit <- interpCircuit circuit
  xs <- mapM readSTRef (circuit^.xs)
  ts <- mapM readSTRef (circuit^.ts)
  us <- mapM readSTRef (circuit^.us)
  assertMessage "runBackward"
    (printf "xs have changed to %d" (valueToInt xs))
    (assert (x == valueToInt xs))
    (return ())
  assertMessage "BackForward"
    (printf "ts are not 1s: %d" (valueToInt ts))
    (assert (1 == valueToInt ts))
    (return ())
  assertMessage "BackForward"
    (printf "us are not 0s: %d" (valueToInt us))
    (assert (0 == valueToInt us))
    (return ())
  return True     

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

simplifyCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
simplifyCircuit c = do
  simplified <- simplifyOP $ c^.circ
  return (set circ simplified c)

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
  let (bs,cs,controls) = shrinkControls bs' cs' controls'
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

peCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
peCircuit c = do
  c <- simplifyCircuit c
  let size = S.length (c^.circ)
  op' <- foldMap (peG size) $ S.zip (c^.circ) (S.fromFunction size (+1))
  return $ set circ op' c

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Making and executing circuits

runPE :: Int -> Integer -> Integer -> Integer -> IO Int
runPE n a m res = pretty $ runST $ do
  circuit <- makeInvExpMod n a m res 
  circuit <- peCircuit circuit
  ts <- mapM readSTRef (circuit^.ts)
  us <- mapM readSTRef (circuit^.us)
  return (zip ts (fromInt (n+1) 1), zip us (fromInt (n+1) 0))
  where
    trueEq (v,b) = isStatic (v^.current) && toBool (v^.current) == b
    
    pretty (ts',us') = do
      putStrLn (take 50 (repeat '_'))
      let ts = filter (not . trueEq) (nub ts')
      let us = filter (not . trueEq) (nub us')
      unless (null ts)
        (mapM_ (\(v,b) -> printf "TS: %s = %s\n" (show v) (if b then "1" else "0")) ts)
      unless (null us)
        (mapM_ (\(v,b) -> printf "US: %s = %s\n" (show v) (if b then "1" else "0")) us)
      putStrLn (take 50 (repeat '_'))
      return (foldr max 0 (map (length . extractVarsF . (^.current) . fst) (ts ++ us)))

----------------------------------------------------------------------------------------
-- Eventual entry point

-- We need to make sure this does not search too far !!!

searchAround :: Integer -> Integer -> Integer -> Maybe Integer
searchAround  y m a =
  if powModInteger a y m == 1 then Just y
  else 
    let s = maybe
            (searchAround (y-2) m a)
            Just
            (searchAround (y+2) m a)
    in if s == Nothing
        then searchAround y m a
        else s

factor :: Integer -> IO (Integer,Integer)
factor m = do
  a <- randomRIO (2,m-1)
  let k = gcd m a
  if k /= 1 then do putStrLn "Lucky!"; return (k , m `div` k)
    else do
    x <- randomRIO (0,m)
    let res = powModInteger a x m 
    let n = ceiling $ logBase 2 (fromInteger m * fromInteger m)
    putStr "Running InvExpMod circuit symbolically with: "
    putStrLn (printf "n = %d; a = %d; m = %d; res = %d" n a m res)
    numberVars <- runPE n a m res
    let y = 2 ^ numberVars
    -- y is close to a multiple of the period
    case searchAround y m a of
      Nothing -> factor m
      Just s ->
        D.trace (printf "Found period %d" s) $
--        let (f1,f2) = (gcd (a ^ (s `div` 2) - 1) m, gcd (a ^ (s `div` 2) + 1) m)
        let (f1,f2) = (gcd (powModInteger a (s `div` 2) m - 1) m,
                       gcd (powModInteger a (s `div` 2) m + 1) m)
        in if f1 == 1 || f2 == 1
           then D.trace "Bad period; restart" (factor m)
           else return (f1,f2)
                              
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
