module SwapArgs.B where
-- Test for refactor of if to case

import Control.Concurrent
import Data.List -- For testing module graph
-- import C         -- For testing module graph

foo x = if (odd x) then "Odd" else "Even"

bob :: a -> b -> Int
bob x y = 1 + 2

-- let foo x = x + 2 in (let foo x = x+1 in  x + foo y)
--    where
--        foo x = x + 1


foo' x = case (odd x) of
  True -> "Odd"
  False -> "Even"

main :: IO ()
main = do
  x <- newEmptyMVar
  putStrLn $ show $ (foo (5 + 42))
  uselessFunc "oi"

mary :: [Integer]
mary = [1,2,3]

h z = (bob z)

data D = A | B String | C

subdecl x = zz x
  where
    zz n = n + 1

uselessFunc text = do 
  x <- newMVar 2
  print text

