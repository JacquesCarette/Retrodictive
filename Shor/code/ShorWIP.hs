{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}

module ShorWIP where

import Data.Maybe
import Data.List

import qualified Data.Sequence as S
import Data.Sequence (Seq, singleton, viewl, ViewL(..), (><))

import Control.Monad 
import Control.Monad.ST
import Data.STRef
  
import Text.Printf
import Test.QuickCheck hiding ((><))
import Control.Exception.Assert
import qualified Debug.Trace as Debug

----------------------------------------------------------------------------------------
-- Simple helpers

debug = True

trace :: String -> a -> a
trace s a = if debug then Debug.trace s a else a

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
-- Circuits are sequences of generalized Toffoli gates

--
-- Values with either static or dynamic information

data Value = Value { name  :: String
                   , value :: Maybe Bool
                   , saved :: Maybe Bool
                   }

defaultValue :: Value
defaultValue =
  Value { name  = ""
        , value = Nothing
        , saved = Nothing
        }

instance Show Value where
  show v = printf "%s %s" (name v) (showmb (value v))
    where showmb Nothing = "_"
          showmb (Just True) = "1"
          showmb (Just False) = "0"

newValue :: String -> Bool -> Value
newValue s b = defaultValue { name = s, value = Just b }

newDynValue :: String -> Value
newDynValue s = defaultValue { name = s, value = Nothing }

isStatic :: Value -> Bool
isStatic (Value {value = Nothing}) = False
isStatic _ = True

extractBool :: Value -> Bool
extractBool (Value { value = Just b }) = b
extractBool _ = error "Expecting a static variable"

negValue :: Value -> Value 
negValue v = v { value = Just (not (extractBool v)) }
                   
valueToInt :: [Value] -> Integer
valueToInt v = toInt $ map extractBool v

-- returns yes/no/unknown as Just True, Just False, Nothing

shrinkControls :: [Bool] -> [Var s] -> [Value] -> ([Bool],[Var s],[Value])
shrinkControls [] [] [] = ([],[],[])
shrinkControls (b:bs) (c:cs) (v:vs)
  | value v == Just b = shrinkControls bs cs vs
  | otherwise =
    let (bs',cs',vs') = shrinkControls bs cs vs
    in (b:bs',c:cs',v:vs')

controlsActive :: [Bool] -> [Value] -> Maybe Bool
controlsActive bs cs =
  if | not r' -> Just False
     | Nothing `elem` r -> Nothing
     | otherwise -> Just True
  where r' = and (catMaybes r)
        r = zipWith f bs cs
        f b (Value { value = Just b' }) = Just (b == b')
        f b _ = Nothing

--
-- Locations where values are stored

type Var s = STRef s Value

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
updateVar var b = do
  v <- readSTRef var
  writeSTRef var (v {value = Just b})
  
updateVars :: [Var s] -> [Bool] -> ST s ()
updateVars vars bs = mapM_ (uncurry updateVar) (zip vars bs)
  
updateDyn :: Var s -> ST s ()
updateDyn var = do
  v <- readSTRef var
  writeSTRef var (v {value = Nothing})

updateDyns :: [Var s] -> ST s ()
updateDyns = mapM_ updateDyn

--
-- Gates and circuits

data GToffoli s = GToffoli [Bool] [Var s] (Var s)
  deriving Eq

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
-- Inverse Shor circuits abstraction for testing

data InvShorCircuit s =
  InvShorCircuit { ps  :: Params
                 , xs  :: [Var s] 
                 , rs  :: [Var s] 
                 , rzs :: [Var s]
                 , os  :: [Var s] 
                 , lzs :: [Var s]
                 , op  :: OP s
                 }

runStatic :: InvShorCircuit s -> Integer -> Integer ->
             ST s (Integer,Integer,Integer)
runStatic isc x res = do
  let n = numberOfBits (ps isc)
  updateVars (xs isc) (fromInt (n+1) x)
  updateVars (rs isc) (fromInt (n+1) res)
  updateVars (rzs isc) (fromInt (n+1) 0)
  interpOP (op isc)
  xvs <- mapM readSTRef (xs isc)
  ovs <- mapM readSTRef (os isc)
  lzvs <- mapM readSTRef (lzs isc)
  return (valueToInt xvs, valueToInt ovs, valueToInt lzvs)

updateDynamic :: InvShorCircuit s -> Integer -> ST s (InvShorCircuit s)
updateDynamic isc res = do
  let n = numberOfBits (ps isc)
  updateDyns (xs isc) 
  updateVars (rs isc) (fromInt (n+1) res)
  updateVars (rzs isc) (fromInt (n+1) 0)
  return isc

----------------------------------------------------------------------------------------
-- Inverse Shor example for testing

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
          { ps = p15a
          , xs = xs
          , rs = us
          , rzs = ts
          , os = ts
          , lzs = us
          , op = S.reverse circuit
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
-- Partial evaluation phases

-- Remove redundant controls
-- If all static controls, execute the instruction

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
     | otherwise -> do -- mark target as unknown
         if saved vt == Nothing
           then writeSTRef t (vt { saved = value vt })
           else return () 
         updateDyn t
         return (S.singleton (GToffoli bs cs t))

restoreSaved :: GToffoli s -> ST s (GToffoli s)
restoreSaved g@(GToffoli bsOrig csOrig t) = do
  vt <- readSTRef t
  if saved vt /= Nothing && value vt == Nothing
    then do writeSTRef t (vt { value = saved vt, saved = Nothing })
            return g
    else return g

-- clunky to force strictness

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
  simplified <- simplifyOP (op c)
  return (c {op = simplified})

-- Collapse g;g to id and simplify afterwards

collapseOP :: OP s -> OP s
collapseOP op = case viewl op of
  EmptyL -> S.empty
  g :< gs -> case viewl gs of 
               EmptyL -> S.singleton g
               g' :< gs' ->
                 if g == g'
                 then collapseOP gs'
                 else S.singleton g >< collapseOP gs

collapseShor :: InvShorCircuit s -> ST s (InvShorCircuit s)
collapseShor c = do
  let collapsed = collapseOP (op c)
  simplified <- simplifyOP collapsed
  return (c {op = simplified})

------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- Run all phases, testing after each phase
-- Test with x = 3, res = 13

pe :: IO ()
pe = 
  let text = runST $ do

        plain <- invShor15

        original <- updateDynamic plain 13
        originalText <- showOP (op original)
        (x,o,z) <- runStatic original 3 13
        assertMessage "Original"
          (printf "x=%d, o=%d, z=%d" x o z)
          (assert (x==3 && o==1 && z==0))
          (return ())

        original <- updateDynamic plain 13
        simplified <- simplifyShor original
        simplifiedText <- showOP (op simplified)
        (x,o,z) <- runStatic simplified 3 13
        assertMessage "Simplified"
          (printf "x=%d, o=%d, z=%d" x o z)
          (assert (x==3 && o==1 && z==0))
          (return ())

        simplified <- updateDynamic simplified 13
        collapsed <- collapseShor simplified
        collapsedText <- showOP (op collapsed)
        (x,o,z) <- runStatic collapsed 3 13
        assertMessage "Collapsed"
          (printf "x=%d, o=%d, z=%d" x o z)
          (assert (x==3 && o==1 && z==0))
          (return ())

        return collapsedText

  in writeFile "tmp.txt" text

------------------------------------------------------------------------------
------------------------------------------------------------------------------

