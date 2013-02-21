module Convoluted where

import Control.Concurrent


swapMVars :: MVar a -> MVar a -> IO ()
swapMVars x y = do
    a <- takeMVar x
    b <- takeMVar y
    putMVar x b
    putMVar y a




main :: IO ()
main = do
    v1 <- newEmptyMVar
    v2 <- newEmptyMVar
    v3 <- newEmptyMVar

    -- ...

    swapMVars v1 v2

    -- ...

    swapMVars v2 v3
