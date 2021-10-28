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

fromInt :: Int -> Integer -> [Bool]
fromInt len n = bits ++ replicate (len - length bits) False 
  where bin 0 = []
        bin n = let (q,r) = quotRem n 2 in toEnum (fromInteger r) : bin q
        bits = bin n

-- Numeric computations
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
-- Circuits are sequences of generalized Toffoli gates

--
-- Values with either static or dynamic information

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
  show v = printf "%s %s" (v^.name) (showmb (v^.value))
    where showmb Nothing = "_"
          showmb (Just True) = "1"
          showmb (Just False) = "0"
--  show v = printf "%s" (name v)

newValue :: String -> Bool -> Value
newValue s b = set name s $ set value (Just b) defaultValue

newDynValue :: String -> Value
newDynValue s = set name s $ set value Nothing defaultValue

isStatic :: Value -> Bool
isStatic v = v^.value /= Nothing

extractBool :: Value -> Bool
extractBool v = maybe (error "expecting a static value") id $ v^.value

-- would it be ok for negValue to 'work' of value is Nothing?
negValue :: Value -> Value 
negValue v = set value (Just (not (extractBool v))) v
                   
valueToInt :: [Value] -> Integer
valueToInt = toInt . map extractBool

--
-- Locations where values are stored

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
-- Gates and circuits

data GToffoli s = GToffoli [Bool] [Var s] (Var s)
  deriving Eq

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

type OP s = Seq (GToffoli s)

showGToffoli :: GToffoli s -> ST s String
showGToffoli (GToffoli bs cs t) = do
  controls <- mapM readSTRef cs
  vt <- readSTRef t
  return $ printf "GToffoli %-15s%-25s(%s)\n" (show bs) (show controls) (show vt)

showOP :: OP s -> ST s String
showOP = foldMap showGToffoli

--

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
  let ca = controlsActive bs controls
  if ca == Just True 
    then writeSTRef t (negValue vt)
    else return ()

interpOP :: OP s -> ST s ()
interpOP = foldMap interpGT

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
-- Some example Shor instances

data Params =
  Params { numberOfBits :: Int
         , base         :: Integer
         , toFactor     :: Integer
         }

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

shorCircuit :: Params -> Integer -> ST s (OP s,[Var s])
shorCircuit (Params {numberOfBits = n, base = a, toFactor = m}) x = do
  gensym <- newSTRef 0
  xs <- newVars gensym "x" (fromInt (n+1) x)
  ts <- newVars gensym "y" (fromInt (n+1) 1)
  us <- newVars gensym "y" (fromInt (n+1) 0)
  circuit <- makeExpMod gensym n a m xs ts us
  return (circuit, if even n then us else ts)

runShor :: Params -> Integer -> Integer
runShor p@(Params { numberOfBits = n, base = a, toFactor = m}) x = runST $ do
  (circuit,rs) <- shorCircuit p x
  interpOP circuit
  res <- mapM readSTRef rs
  return (valueToInt res)

-- 
-- *ShorWIP> map (runShor p15a) [0..10]
-- [1,7,4,13,1,7,4,13,1,7,4]

----------------------------------------------------------------------------------------
-- Inverse Shor circuits abstraction for testing PE; can be run with
-- all static parameters or with mixed static and dynamic parameters
-- 

data InvShorCircuit s =
  InvShorCircuit { _ps  :: Params
                 , _xs  :: [Var s] 
                 , _rs  :: [Var s] 
                 , _rzs :: [Var s]
                 , _os  :: [Var s] 
                 , _lzs :: [Var s]
                 , _op  :: OP s
                 }

makeLenses ''InvShorCircuit

runStatic :: InvShorCircuit s -> Integer -> Integer ->
             ST s (Integer,Integer,Integer)
runStatic isc x res = do
  let n = numberOfBits $ isc^.ps
  updateVars (isc^.xs) (fromInt (n+1) x)
  updateVars (isc^.rs) (fromInt (n+1) res)
  updateVars (isc^.rzs) (fromInt (n+1) 0)
  interpOP $ isc^.op
  xvs <- mapM readSTRef $ isc^.xs
  ovs <- mapM readSTRef $ isc^.os
  lzvs <- mapM readSTRef $ isc^.lzs
  return (valueToInt xvs, valueToInt ovs, valueToInt lzvs)

updateDynamic :: InvShorCircuit s -> Integer -> ST s ()
updateDynamic isc res = do
  let n = numberOfBits $ isc^.ps
  updateDyns $ isc^.xs
  updateVars (isc^.rs) (fromInt (n+1) res)
  updateVars (isc^.rzs) (fromInt (n+1) 0)

----------------------------------------------------------------------------------------
-- Inverse Shor 15 example for testing

invShor15 :: ST s (InvShorCircuit s)
invShor15 = do
  let p = p15a
  let n = numberOfBits p -- 4
  let a = base p
  let m = toFactor p
  gensym <- newSTRef 0
  xs <- newDynVars gensym "x" (n+1)
  ts <- newVars gensym "y" (fromInt (n+1) 0)
  us <- newDynVars gensym "y" (n+1)
  circuit <- makeExpMod gensym n a m xs ts us
  return (InvShorCircuit
          { _ps = p15a
          , _xs = xs
          , _rs = us
          , _rzs = ts
          , _os = ts
          , _lzs = us
          , _op = S.reverse circuit
          })

testRunStaticShor15 :: Bool  
testRunStaticShor15 = runST $ do
  isc <- invShor15
  (x0,o0,z0) <- runStatic isc 0 1
  (x1,o1,z1) <- runStatic isc 1 7
  (x2,o2,z2) <- runStatic isc 2 4
  (x3,o3,z3) <- runStatic isc 3 13
  return (x0 == 0 && x1 == 1 && x2 == 2 && x3 == 3 &&
          o0 == 1 && o1 == 1 && o2 == 1 && o3 == 1 &&
          z0 == 0 && z1 == 0 && z2 == 0 && z3 == 0)
  
----------------------------------------------------------------------------------------
-- Helpers for simplification of circuits

-- Type for a controlled variable with a value
data CVV s = CVV { control :: Bool
                 , var     :: Var s
                 , val     :: Value
                 }

-- returns yes/no/unknown as Just True, Just False, Nothing

shrinkControls :: [Bool] -> [Var s] -> [Value] -> ([Bool],[Var s],[Value])
shrinkControls [] [] [] = ([],[],[])
shrinkControls (b:bs) (c:cs) (v:vs)
  | v^.value == Just b = shrinkControls bs cs vs
  | otherwise =
    let (bs',cs',vs') = shrinkControls bs cs vs
    in (b:bs',c:cs',v:vs')

----------------------------------------------------------------------------------------
-- Partial evaluation phases

frontN :: Int -> Seq a -> ([a],Seq a)
frontN 0 seq = ([],seq)
frontN n seq = case viewl seq of
  EmptyL -> ([],S.empty)
  a :< as -> let (f,as') = frontN (n-1) as in (a:f, as')

-- Simplify phase:
-- 
-- shrinkControls: removes redundant controls
-- then test whether controlsActive:
--   if definitely active => execute the instruction; emit nothing
--   if definitely not active => eliminate the instruction; emit nothing
--   if unknown => emit instruction as residual

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
         return (S.singleton (GToffoli bs cs t))

restoreSaved :: GToffoli s -> ST s (GToffoli s)
restoreSaved g@(GToffoli bsOrig csOrig t) = do
  vt <- readSTRef t
  let vs = vt^.saved
  if vs /= Nothing && vt^.value == Nothing
    then do writeSTRef t (set saved Nothing $ set value vs vt)
            return g
    else return g

simplifyOP :: OP s -> ST s (OP s)
simplifyOP op = case viewl op of
  EmptyL -> return S.empty
  g :< gs -> do
    g' <- simplifyG g
    gs' <- simplifyOP gs
    case viewl (g' >< gs') of
      EmptyL -> return S.empty
      g :< gs -> do
        g' <- restoreSaved g
        return (S.singleton g' >< gs)

simplifyShor :: InvShorCircuit s -> ST s (InvShorCircuit s)
simplifyShor c = do
  simplified <- simplifyOP $ c^.op
  return (set op simplified c)

-- Collapse phase:
-- 
-- Collapse g;g to id
-- Collapse x;cx;x to ncx
-- Simplify afterwards

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

collapseShor :: InvShorCircuit s -> ST s (InvShorCircuit s)
collapseShor c = do
  let collapsed = collapseOP $ c^.op
  simplified <- simplifyOP collapsed
  return $ set op simplified c


-- Do full partial evaluation

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

peShor :: InvShorCircuit s -> ST s (InvShorCircuit s)
peShor c = do
  op' <- peOP $ c^.op
  return $ set op op' c

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- Run all phases, testing after each phase
-- Test with x = 3, res = 13

pe :: IO ()
pe = writeFile "tmp.txt" $ runST $ do 
  circuit <- invShor15
  updateDynamic circuit 13        ; check "Original"   circuit
  circuit <- simplifyShor circuit ; check "Simplified" circuit
  circuit <- collapseShor circuit ; check "Collpased"  circuit
  circuit <- peShor       circuit ; check "PE"         circuit
  showOP $ circuit^.op
  where
    check :: String -> InvShorCircuit s -> ST s ()
    check msg op = do
      (x,o,z) <- runStatic op 3 13
      assertMessage msg
        (printf "x=%d, o=%d, z=%d" x o z)
        (assert (x==3 && o==1 && z==0))
        (return ())
      updateDynamic op 13

------------------------------------------------------------------------------
------------------------------------------------------------------------------


