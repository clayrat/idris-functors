module Main

import KleisliArr.Basic
import KleisliArr.Free
import Control.IOExcept

main : IO ()
main = do args <- getArgs
          case args of
            [_, fn] => ioe_run (runFH $ fileContents fn) (putStrLn . show) (putStrLn . show)  
            _        => putStrLn "Wrong args"

