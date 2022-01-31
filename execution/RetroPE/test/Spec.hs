import PEZ 
import Test.QuickCheck

main :: IO ()
main = do 
  quickCheck f1xorf2
  quickCheck notf2
  quickCheck f1andf2
  putStrLn "Done"
  
-- From the Wikipedia page for Algebraic Normal Form  
  
one = Ands []
x = Ands [ "x" ]
y = Ands [ "y" ]
xy = x &&& y

f1 = Formula [ one, x ]
f2 = Formula [ one, x, y ]

f1xorf2 :: Bool
f1xorf2 = f1 `fxor` f2 == anf (Formula [ y ])  

notf2 :: Bool
notf2 = fnot f2 == anf (Formula [ x, y ])

f1andf2 :: Bool 
f1andf2 = f1 `fand` f2 == anf (Formula [ one, x, y, xy ])