module ShorBase3 where

import Data.List

------------------------------------------------------------------------------
-- Manually optimized shor 21 using qutrits

-- Gates (defined in: https://arxiv.org/pdf/1512.03824.pdf)
-- 
-- Let delta (x,y) = if x == y then 1 else 0
-- 
--     X (x) = x+1 
--  CX (x,y) = (x , y + delta(x,2))
-- SUM (x,y) = (x, x+y) 
-- 


data Gate = X Int | SUM Int Int | CX Int Int

type State = [Int]

upd :: State -> Int -> (Int -> Int) -> State
upd st i f = st0 ++ (f x : st1)
  where (st0,(x:st1)) = splitAt i st

delta x y = if x == y then 1 else 0

plus :: Int -> Int -> Int
x `plus` y = (x + y) `mod` 3

inc :: Int -> Int
inc x = x `plus` 1

eval :: Gate -> State -> State
eval (X i) st = upd st i inc
eval (SUM i j) st = upd st j (\y -> st !! i `plus` y)
eval (CX i j) st = upd st j (\y -> delta (st !! i) 2 `plus` y)

evalC :: State -> [Gate] -> State
evalC = foldr eval

---

circ :: [Gate]
circ = [ X 4, SUM 1 3, CX 1 2 ]

qst :: [State]
qst = [ [x,y,0,0,0] | x <- [0,1,2], y <- [0,1,2] ]

run = map (\st -> (st, evalC st circ)) qst

{--

[

 ([0,0,0,0,0],[0,0,0,0,1]),
 ([1,0,0,0,0],[1,0,0,0,1]),
 ([2,0,0,0,0],[2,0,0,0,1]),

 ([0,1,0,0,0],[0,1,0,1,1]),
 ([1,1,0,0,0],[1,1,0,1,1]),
 ([2,1,0,0,0],[2,1,0,1,1]),

 ([0,2,0,0,0],[0,2,1,2,1]),
 ([1,2,0,0,0],[1,2,1,2,1]),
 ([2,2,0,0,0],[2,2,1,2,1])

]

Compare to:

*EvalZ> let fc x = runExpMod 5 4 21 x
*EvalZ> mapM_ fc [0..8]
Result = 1
Result = 4
Result = 16
...

*QAlgos> printResult $ runST $ expModCircuit FB.formRepr 0 5 4 21 1

Generalized Toffoli Gates with 3 controls = 864
Generalized Toffoli Gates with 2 controls = 7416
Generalized Toffoli Gates with 1 controls = 7344

1 \oplus x0 \oplus x1 \oplus x2 \oplus x0x2 \oplus x0x1x2 \oplus x3 \oplus x1x3 \oplus x0x1x3 \oplus x0x2x3 \oplus x1x2x3 \oplus x4 \oplus x0x4 \oplus x0x1x4 \oplus x2x4 \oplus x1x2x4 \oplus x0x1x2x4 \oplus x0x3x4 \oplus x1x3x4 \oplus x2x3x4 \oplus x0x2x3x4 \oplus x0x1x2x3x4 \oplus x5 \oplus x1x5 \oplus x0x1x5 \oplus x0x2x5 \oplus x1x2x5 \oplus x3x5 \oplus x0x3x5 \oplus x0x1x3x5 \oplus x2x3x5 \oplus x1x2x3x5 \oplus x0x1x2x3x5 \oplus x0x4x5 \oplus x1x4x5 \oplus x2x4x5 \oplus x0x2x4x5 \oplus x0x1x2x4x5 \oplus x3x4x5 \oplus x1x3x4x5 \oplus x0x1x3x4x5 \oplus x0x2x3x4x5 \oplus x1x2x3x4x5 = 1

x1 \oplus x0x1 \oplus x0x2 \oplus x1x2 \oplus x3 \oplus x0x3 \oplus x0x1x3 \oplus x2x3 \oplus x1x2x3 \oplus x0x1x2x3 \oplus x0x4 \oplus x1x4 \oplus x2x4 \oplus x0x2x4 \oplus x0x1x2x4 \oplus x3x4 \oplus x1x3x4 \oplus x0x1x3x4 \oplus x0x2x3x4 \oplus x1x2x3x4 \oplus x5 \oplus x0x5 \oplus x0x1x5 \oplus x2x5 \oplus x1x2x5 \oplus x0x1x2x5 \oplus x0x3x5 \oplus x1x3x5 \oplus x2x3x5 \oplus x0x2x3x5 \oplus x0x1x2x3x5 \oplus x4x5 \oplus x1x4x5 \oplus x0x1x4x5 \oplus x0x2x4x5 \oplus x1x2x4x5 \oplus x3x4x5 \oplus x0x3x4x5 \oplus x0x1x3x4x5 \oplus x2x3x4x5 \oplus x1x2x3x4x5 \oplus x0x1x2x3x4x5 = 0

x0 \oplus x0x1 \oplus x2 \oplus x1x2 \oplus x0x1x2 \oplus x0x3 \oplus x1x3 \oplus x2x3 \oplus x0x2x3 \oplus x0x1x2x3 \oplus x4 \oplus x1x4 \oplus x0x1x4 \oplus x0x2x4 \oplus x1x2x4 \oplus x3x4 \oplus x0x3x4 \oplus x0x1x3x4 \oplus x2x3x4 \oplus x1x2x3x4 \oplus x0x1x2x3x4 \oplus x0x5 \oplus x1x5 \oplus x2x5 \oplus x0x2x5 \oplus x0x1x2x5 \oplus x3x5 \oplus x1x3x5 \oplus x0x1x3x5 \oplus x0x2x3x5 \oplus x1x2x3x5 \oplus x4x5 \oplus x0x4x5 \oplus x0x1x4x5 \oplus x2x4x5 \oplus x1x2x4x5 \oplus x0x1x2x4x5 \oplus x0x3x4x5 \oplus x1x3x4x5 \oplus x2x3x4x5 \oplus x0x2x3x4x5 \oplus x0x1x2x3x4x5 = 0


--}

------------------------------------------------------------------------------


