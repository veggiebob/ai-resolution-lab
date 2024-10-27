{- debugging purposes only, not required for build -}


module Main where

import System.Environment (getArgs) 
import Lib (main', doResolution)

data Say = Yes | No
instance Show Say where
    show Yes = "yes"
    show No = "no"

say :: Bool -> Say
say True = Yes
say False = No

main :: IO ()
main = do
    args <- getArgs
    putStrLn "file parse output:"
    main' id (head args)
    putStrLn "result:"
    main' ((\(r, a) -> (r, say $ not a)) . doResolution) (head args)
