module QFT where
-- Do classical simulation of QFT

-- Shor:

-- Stage I and measure: easy to simulate classically; just pick a random number

-- Stage I and II and measure: easy to simulate classically; just pick
-- a random number and apply expmod

-- Stage III and measure: can be done classically apparently

-- Some simple state II (let's call it II') and then III: can
-- apparently also be done classically

-- So what gives? 

-- Sec. 7.4.2 of book shows that Grover has the same pattern; might be able to do
-- something with it

-- if we get rid of ccx, becomes 2SAT or some decidable graph
-- algorithm or some variant of Ising model that is decidable
