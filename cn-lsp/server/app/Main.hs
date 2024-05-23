module Main where

import Control.Monad (void)
import Language.LSP.Server qualified as LSP
import Server (mkServer)
import System.Environment (getArgs)

main :: IO ()
main =
  do
    args <- getArgs
    case args of
      [logFile] -> void (LSP.runServer (mkServer logFile))
      _ -> error ("unexpected arguments: " <> show args)
