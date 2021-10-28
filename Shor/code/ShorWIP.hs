{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module ShorWIP where

import Data.Maybe (catMaybes, maybe)

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
    loop 0 _ _ _ = error "Inputs not coprime"
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

data Value = Value { _name  :: String
                   , _value :: Maybe Bool
                   , _saved :: Maybe Bool
                   }

makeLenses ''Value

defaultValue :: Value
defaultValue =
  Value { _name  = ""
        , _value = Nothing
        , _saved = Nothing
        }

instance Show Value where
{--
  show v = printf "%s %s" (v^.name) (showmb (v^.value))
    where showmb Nothing = "_"
          showmb (Just True) = "1"
          showmb (Just False) = "0"
--}
  show v = printf "%s" (v^.name)

newValue :: String -> Bool -> Value
newValue s b = set name s $ set value (Just b) defaultValue

newDynValue :: String -> Value
newDynValue s = set name s $ set value Nothing defaultValue

isStatic :: Value -> Bool
isStatic v = v^.value /= Nothing

extractBool :: Value -> Bool
extractBool v = maybe (error "expecting a static value") id $ v^.value

-- would it be ok for negValue to 'work' of value is Nothing?
-- yes but raising an error for now to catch unintended uses

negValue :: Value -> Value 
negValue v = set value (Just (not (extractBool v))) v
                   
valueToInt :: [Value] -> Integer
valueToInt = toInt . map extractBool

--
-- Locations where values are stored
-- ---------------------------------

type Var s = STRef s Value

-- Stateful functions to deal with variables

newVar :: STRef s Int -> String -> Bool -> ST s (Var s)
newVar gensym s b = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newValue (s ++ (show k)) b)

newVars :: STRef s Int -> String -> [Bool] -> ST s [Var s]
newVars gensym s = mapM (newVar gensym s)

newDynVar :: STRef s Int -> String -> ST s (Var s)
newDynVar gensym s = do
  k <- readSTRef gensym
  writeSTRef gensym (k+1)
  newSTRef (newDynValue (s ++ (show k)))

newDynVars :: STRef s Int -> String -> Int -> ST s [Var s]
newDynVars gensym s n = replicateM n (newDynVar gensym s)

updateVar :: Var s -> Bool -> ST s ()
updateVar var b = modifySTRef var (set value (Just b))
  
updateVars :: [Var s] -> [Bool] -> ST s ()
updateVars vars bs = mapM_ (uncurry updateVar) (zip vars bs)
  
updateDyn :: Var s -> ST s ()
updateDyn var = modifySTRef var (set value Nothing)

updateDyns :: [Var s] -> ST s ()
updateDyns = mapM_ updateDyn

--
-- Generalized Toffoli gates
-- -------------------------

data GToffoli s = GToffoli [Bool] [Var s] (Var s)
  deriving Eq

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %-15s%-25s(%s)\n"
    (show (map fromEnum bs))
    (show controls)
    (show vt)

target :: GToffoli s -> Var s
target (GToffoli _ _ t) = t

flipControl :: GToffoli s -> GToffoli s
flipControl (GToffoli [b] [v] t) = GToffoli [not b] [v] t

xcxx :: GToffoli s -> GToffoli s -> GToffoli s -> Bool
xcxx (GToffoli [] [] t0) (GToffoli [b] [t1] t2) (GToffoli [] [] t3)
  | t0 == t1 && t0 == t1 && t0 == t3 && t0 /= t2 = True
  | otherwise = False
xcxx _ _ _ = False

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

makeAdder :: STRef s Int -> Int -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdder gensym n as bs = do
  cs <- newVars gensym "y" (fromInt n 0)
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

makeAdderMod :: STRef s Int -> Int -> Integer -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeAdderMod gensym n m as bs = do
  ms <- newVars gensym "y" (fromInt (n+1) m)
  ms' <- newVars gensym "y" (fromInt (n+1) m)
  t <- newVar gensym "y" False
  adderab <- makeAdder gensym n as bs
  addermb <- makeAdder gensym n ms bs
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

makeCMulMod :: STRef s Int -> Int -> Integer -> Integer ->
               Var s -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeCMulMod gensym n a m c xs ts = do
  ps <- newVars gensym "y" (fromInt (n+1) 0)
  as <- mapM
          (\a -> newVars gensym "y" (fromInt (n+1) a))
          (take (n+1) (doublemods a m))
  adderPT <- makeAdderMod gensym n m ps ts
  return (loop adderPT as xs ps)
    where loop adderPT [] [] ps =
            ncop c (copyOP xs ts) 
          loop adderPT (a:as) (x:xs) ps =
            ccop (copyOP a ps) [c,x] ><
            adderPT ><
            ccop (copyOP a ps) [c,x] ><
            loop adderPT as xs ps

makeExpMod :: STRef s Int -> Int -> Integer -> Integer ->
              [ Var s ] -> [ Var s ] -> [ Var s ] -> ST s (OP s)
makeExpMod gensym n a m xs ts us = do
  let sqs = take (n+1) (sqmods a m)
  let invsqs = take (n+1) (invsqmods a m)
  makeStages 0 n sqs invsqs m xs ts us
    where
      makeStages i n [] [] m [] ts us = return S.empty
      makeStages i n (sq:sqs) (invsq:invsqs) m (c:cs) ts us
        | even i = do
            mulsqMod <- makeCMulMod gensym n sq m c ts us
            mulinvsqMod <- makeCMulMod gensym n invsq m c us ts
            rest <- makeStages (i+1) n sqs invsqs m cs ts us
            return (mulsqMod ><
                    S.reverse mulinvsqMod ><
                    rest)
        | otherwise = do
            mulsqMod <- makeCMulMod gensym n sq m c us ts
            mulinvsqMod <- makeCMulMod gensym n invsq m c ts us
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
     | otherwise -> Just True
  where r' = and (catMaybes r)
        r = zipWith f bs cs
        f b v = fmap (\b' -> b == b') $ v^.value

interpGT :: GToffoli s -> ST s ()
interpGT (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  if controlsActive bs controls == Just True 
    then writeSTRef t (negValue vt)
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

makeCircuitDynamic :: InvExpModCircuit s -> Integer -> ST s ()
makeCircuitDynamic isc res = do
  let n = numberOfBits $ isc^.ps
  updateDyns $ isc^.xs
  updateVars (isc^.rs) (fromInt (n+1) res)
  updateVars (isc^.rzs) (fromInt (n+1) 0)

----------------------------------------------------------------------------------------
-- Type for a controlled variable with a value
-- ??

data CVV s = CVV { control :: Bool
                 , var     :: Var s
                 , val     :: Value
                 }

----------------------------------------------------------------------------------------
-- Partial evaluation phases

-- Simplify phase
-- --------------
-- 
-- shrinkControls: removes redundant controls
-- then test whether controlsActive:
--   if definitely active => execute the instruction; emit nothing
--   if definitely not active => eliminate the instruction; emit nothing
--   if unknown => emit instruction as residual

shrinkControls :: [Bool] -> [Var s] -> [Value] -> ([Bool],[Var s],[Value])
shrinkControls [] [] [] = ([],[],[])
shrinkControls (b:bs) (c:cs) (v:vs)
  | v^.value == Just b = shrinkControls bs cs vs
  | otherwise =
    let (bs',cs',vs') = shrinkControls bs cs vs
    in (b:bs',c:cs',v:vs')

restoreSaved :: GToffoli s -> ST s (GToffoli s)
restoreSaved g@(GToffoli bsOrig csOrig t) = do
  vt <- readSTRef t
  let vs = vt^.saved
  if vs /= Nothing && vt^.value == Nothing
    then do writeSTRef t (set saved Nothing $ set value vs vt)
            return g
    else return g

simplifyG :: GToffoli s -> ST s (OP s)
simplifyG (GToffoli bsOrig csOrig t) = do
  controlsOrig <- mapM readSTRef csOrig
  vt <- readSTRef t
  let (bs,cs,controls) = shrinkControls bsOrig csOrig controlsOrig
  let ca = controlsActive bs controls
  if | ca == Just True && isStatic vt -> do
         writeSTRef t (negValue vt)
         return S.empty
     | ca == Just False ->
         return S.empty
     | otherwise -> do
         -- save value of target; mark it as unknown for remainder of phase
         if vt^.saved == Nothing
           then writeSTRef t (set saved (vt^.value) vt)
           else return () 
         updateDyn t
         return $ S.singleton (GToffoli bs cs t)

simplifyOP :: OP s -> ST s (OP s)
simplifyOP op = do
  op <- foldMap simplifyG op
  mapM restoreSaved op

simplifyCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
simplifyCircuit c = do
  simplified <- simplifyOP $ c^.circ
  return (set circ simplified c)

-- Collapse phase
-- --------------

-- Collapse g;g to id
-- Collapse x;cx;x to ncx
-- Simplify afterwards

frontN :: Int -> Seq a -> ([a],Seq a)
frontN 0 seq = ([],seq)
frontN n seq = case viewl seq of
  EmptyL -> ([],S.empty)
  a :< as -> let (f,as') = frontN (n-1) as in (a:f, as')

collapseOP :: OP s -> OP s
collapseOP op = case frontN 3 op of
  ([],_)            -> op
  ([g],_)           -> op
  ([g1,g2],_) 
    | g1 == g2      -> S.empty
    | otherwise     -> op
  ([g1,g2,g3],gs) 
    | g1 == g2      -> collapseOP (S.singleton g3 >< gs)
    | xcxx g1 g2 g3 -> S.singleton (flipControl g2) >< collapseOP gs
    | otherwise     -> S.singleton g1 >< collapseOP (S.fromList [g2,g3] >< gs)

collapseCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
collapseCircuit c = do
  let collapsed = collapseOP $ c^.circ
  simplified <- simplifyOP collapsed
  return $ set circ simplified c

-- Do full partial evaluation
-- --------------------------

peG :: GToffoli s -> ST s (OP s)
peG g@(GToffoli bs cs t) = do 
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  case controls of
    -- [ Value { value = Nothing } ] ->
    [ v ] | v^.value == Nothing ->
      case (head bs, vt^.value) of
        (True, Nothing) -> return (S.singleton g) 
        _ -> return (S.singleton g)
    _ -> return (S.singleton g)
        
{--

cx(x=DYN,y=0) ==> (x=DYN,y=x)

Aliasing???

pass around a hashmap : String -> String
where these are the gensym'ed names
we would add y -> x in the hashmap
etc

--}


peOP :: OP s -> ST s (OP s)
peOP op = case viewl op of
  EmptyL -> return S.empty
  g :< gs -> do
    g' <- peG g
    gs' <- peOP gs
    case viewl (g' >< gs') of
      EmptyL -> return S.empty
      g :< gs -> do
        g' <- restoreSaved g
        return (S.singleton g' >< gs)

peCircuit :: InvExpModCircuit s -> ST s (InvExpModCircuit s)
peCircuit c = do
  op' <- peOP $ c^.circ
  return $ set circ op' c

--
-- Run all phases
-- --------------

pe :: InvExpModCircuit s -> Integer -> ST s (InvExpModCircuit s)
pe circuit res = do
  makeCircuitDynamic circuit res
  return circuit >>= simplifyCircuit >>= collapseCircuit >>= peCircuit

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Helpers for testing

-- Construct an expmod circuit

expModCircuit :: Params -> Integer -> ST s (OP s,[Var s])
expModCircuit (Params {numberOfBits = n, base = a, toFactor = m}) x = do
  gensym <- newSTRef 0
  xs <- newVars gensym "x" (fromInt (n+1) x)
  ts <- newVars gensym "y" (fromInt (n+1) 1)
  us <- newVars gensym "y" (fromInt (n+1) 0)
  circuit <- makeExpMod gensym n a m xs ts us
  return (circuit, if even n then us else ts)

-- Run an expMod circuit

runExpMod :: Params -> Integer -> Integer
runExpMod ps x = runST $ do
  (circuit,rs) <- expModCircuit ps x
  interpOP circuit
  res <- mapM readSTRef rs
  return (valueToInt res)

-- Run a given invExpMod circuit with all static values

runInvExpMod :: InvExpModCircuit s -> Integer -> Integer ->
             ST s (Integer,Integer,Integer)
runInvExpMod isc x res = do
  let n = numberOfBits $ isc^.ps
  updateVars (isc^.xs) (fromInt (n+1) x)
  updateVars (isc^.rs) (fromInt (n+1) res)
  updateVars (isc^.rzs) (fromInt (n+1) 0)
  interpOP $ isc^.circ
  xvs <- mapM readSTRef $ isc^.xs
  ovs <- mapM readSTRef $ isc^.os
  lzvs <- mapM readSTRef $ isc^.lzs
  return (valueToInt xvs, valueToInt ovs, valueToInt lzvs)

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Examples

p15a = Params {
  numberOfBits = 4, 
  base         = 7, 
  toFactor     = 15
  }

p15b = Params {
  numberOfBits = 5, 
  base         = 7, 
  toFactor     = 15
  }

p21 = Params {
  numberOfBits = 6, 
  base         = 5, 
  toFactor     = 21
  }

p323 = Params {
  numberOfBits = 10, 
  base         = 49, 
  toFactor     = 323
  }

-- 
-- ShorWIP> map (runExpMod p15a) [0..10]
-- [1,7,4,13,1,7,4,13,1,7,4]
-- 

-- Example invExpMod circuit

invExpMod15 :: ST s (InvExpModCircuit s)
invExpMod15 = do
  let ps = p15a
  let n = numberOfBits ps -- 4
  let a = base ps
  let m = toFactor ps
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" (n+1)
  ts <- newVars gensym "y" (fromInt (n+1) 0)
  us <- newDynVars gensym "y" (n+1)
  circuit <- makeExpMod gensym n a m xs ts us
  return (InvExpModCircuit
          { _ps   = p15a
          , _xs   = xs
          , _rs   = us
          , _rzs  = ts
          , _os   = ts
          , _lzs  = us
          , _circ = S.reverse circuit
          })

-- Run PE phases with dynamic information
-- and test after each phase

pe15PrintTest :: IO ()
pe15PrintTest = writeFile "tmp.txt" $ runST $ do
  circuit <- invExpMod15
  makeCircuitDynamic circuit 13      ; check "Original (x=3,res=13)"   circuit 3 13
  circuit <- simplifyCircuit circuit ; check "Simplified (x=3,res=13)" circuit 3 13
  circuit <- collapseCircuit circuit ; check "Collapsed (x=3,res=13)"  circuit 3 13
  circuit <- peCircuit       circuit ; check "PE (x=3,res=13)"         circuit 3 13
  showOP $ circuit^.circ
  where
    check :: String -> InvExpModCircuit s -> Integer -> Integer -> ST s ()
    check msg op x res = do
      (rx,ro,rz) <- runInvExpMod op x res
      assertMessage msg
        (printf "x=%d, o=%d, z=%d" rx ro rz)
        (assert (rx==x && ro==1 && rz==0))
        (return ())
      makeCircuitDynamic op res

------------------------------------------------------------------------------
------------------------------------------------------------------------------
