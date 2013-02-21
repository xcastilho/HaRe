module Transact.SimpleConfusion where

import Control.Concurrent

main :: IO ()
main = do
    v1 <- newEmptyMVar
    v2 <- newEmptyMVar

    -- ...

    let v3 = id v2

    -- ...

    let v4 = id v1

    -- ...

    takeMVar v1 >>= putStrLn

