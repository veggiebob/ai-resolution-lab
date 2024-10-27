{-

Author: Jacob Bowman (jb6248@rit.edu)
CSCI-331 Intro to AI Lab 2

Run this file in this root directory using:

```
ghc Main
./Main <filename>
```

-}



module Main where

import System.Environment (getArgs) 
import Lib (main', doResolution)

-- lol
data Say = Yes | No
instance Show Say where
    show Yes = "yes"
    show No = "no"

say :: Bool -> Say
say True = Yes
say False = No

cmain' :: String -> IO ()
cmain' fp = do
    main' (say . not . snd . doResolution) fp

main :: IO ()
main = do
    args <- getArgs
    main' (say . not . snd . doResolution) (head args)
