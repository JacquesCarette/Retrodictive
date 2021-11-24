{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module ExpMod where

import Control.Monad 
import Control.Monad.ST
import Control.Lens hiding (op,(:<))
import Control.Exception.Assert (assert, assertMessage)

import Data.STRef
import qualified Data.Sequence as S
import Data.Sequence (Seq,singleton,(><))
import Data.Maybe (catMaybes)

import Text.Printf (printf)

--

import Numeric
import ANF

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
----------------------------------------------------------------------------------------

