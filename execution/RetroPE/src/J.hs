module J where

import Prelude hiding (not)
import Debug.Trace
import Data.List

{--
X gate for qudits is addition modulo p:
https://arxiv.org/pdf/2008.00959.pdf
--}

-- base 3

bin :: Integer -> Integer -> [Integer]
bin b 0 = []
bin b n = let (q,r) = quotRem n b in toEnum (fromInteger r) : bin b q

{--

Keep known wires as bits; state of unknown wires represented in different
number bases

--}


data State = State Int [Int]
  deriving Show

upd :: Int -> Int -> State -> State
upd g v s@(State p ns) = trace (show s) $ 
  State p (take g ns ++ [v] ++ drop (g+1) ns)

not :: Int -> State -> State
not g s@(State p ns) = upd g v s where
    v = ((ns !! g) + 1) `mod` p

cnot :: Int -> Int -> State -> State
cnot c g s@(State p ns) =  upd g v s where
    v = ((ns !! c) + (ns !! g)) `mod` p

ccnot :: Int -> Int -> Int -> State -> State
ccnot c1 c2 g s@(State p ns) =  upd g v s where
    v = (((ns !! c1) * (ns !! c2)) + (ns !! g))  `mod` p

shor = cnot 4 3 .
       ccnot 0 3 4 .
       cnot 4 3 .
       not 4 .
       ccnot 0 4 3 .
       not 4 .
       cnot 4 3 .
       ccnot 1 3 4 .
       cnot 4 3 .
       cnot 1 4 .
       cnot 2 4

s2 c0 c1 c2 = State 2 [c0,c1,c2,0,0]
s3 c0 c1 c2 = State 3 [c0,c1,c2,0,0]

{--
base 2

000 => 00
011 => 00
110 => 00

001 => 01
100 => 01
111 => 01

010 => 10
101 => 10


base 3: 

--}

allT = [ [a,b,c] | a <- [0,1,2], b <- [0,1,2], c <- [0,1,2]]

f t = shor (State 3 (t ++ [0,0]))

g t = let State 3 [_,_,_,x,y] = f t in [x,y]


res = map (\t -> (t,g t)) allT

sres = sortBy (\ (a,b) (c,d) -> compare b d) res

fres = groupBy (\ (a,b) (c,d) -> b == d) sres

{--

[([0,1,1],[0,0]),([2,0,1],[0,0])],

[([0,0,2],[0,1]),([1,2,0],[0,1])]

[([0,2,0],[0,2]),([1,1,0],[0,2]),([2,1,1],[0,2])]

[([1,2,2],[1,0]),([2,1,0],[1,0])]

[([0,0,0],[1,2]),([0,1,2],[1,2]),([0,2,1],[1,2]),([1,1,1],[1,2]),([2,0,2],[1,2])]

[([0,0,1],[2,0]),([1,0,2],[2,0]),([2,2,2],[2,0])]

[([0,1,0],[2,1]),([1,0,1],[2,1]),([2,0,0],[2,1]),([2,1,2],[2,1]),([2,2,1],[2,1])]

[([0,2,2],[2,2]),([1,0,0],[2,2]),([1,1,2],[2,2]),([1,2,1],[2,2]),([2,2,0],[2,2])]]

--}

{--

Retro with c0 c1 c2 0 0

c0 c1 c2 0 0
==>
c0 c1 c2 0 0
==>
c0 c1 c2 0 0
==>
c0 c1 c2 0 1
==>
c0 c1 c2 c0 1
==>
c0 c1 c2 c0 0
==>
c0 c1 c2 c0 c0c1
==>
c0 c1 c2 (c0+c0c1) c0c1
==>
c0 c1 c2 (c0+c0c1) (c1+c0c1)
==>
c0 c1 c2 (c0+c0c1) (c1+c2+c0c1)

---

c0+c0c1 = 0
c1+c2+c0c1 = 0

c0=0, c1=c2 => 000, 011
c0=1, c1=1, c2=0 => 110


--}

{--

Retro with c0 c1 c2 0 1

c0 c1 c2 0 1
==>
c0 c1 c2 1 1
==>
c0 c1 c2 1 c0
==>
c0 c1 c2 (1+c0) c0
==>
c0 c1 c2 (1+c0) (1+c0)
==>
c0 c1 c2 (1+c0) (1+c0)
==>
c0 c1 c2 (1+c0) c0
==>
c0 c1 c2 1 c0
==>
c0 c1 c2 1 (c0+c1)
==>
c0 c1 c2 (1+c0+c1) (c0+c1)
==>
c0 c1 c2 (1+c0+c1) c0
==>
c0 c1 c2 (1+c0+c1) (c0+c2)

--

c0+c2 = 0
1+c0+c1 = 0

c0 = 0, c2 = 0, c1 = 1 => 010
c0 = 1, c1 = 0 => 100, 101

--}

{--

Retro with c0 c1 c2 1 0

--}
