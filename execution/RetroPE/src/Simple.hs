module Simple where

------------------------------------------------------------------------------

-- demonstration of generate-and-test

generate :: Int -> [(Int,Int,Int)]
generate n =  [(x,y,z) | x <- [1..n], y <- [1..n], z <- [1..n]]

test :: Int -> [(Int,Int,Int)] -> [(Int,Int,Int)]
test s nums = [(x,y,z) | (x,y,z) <- nums, x /= y, x /= z, y /= z, x+y+z == s]

find :: Int -> Int -> (Int,Int,Int)
find s =  head . test s . generate

-- demonstration of partial evaluation

power :: Int -> Int -> Int
power a n
  | n == 0 = 1
  | n == 1 = a
  | even n = 
     let r = power a (n `div` 2) in 
     r * r 
  | otherwise = 
     let r = power a (n-1) in
     a * r

------------------------------------------------------------------------------
