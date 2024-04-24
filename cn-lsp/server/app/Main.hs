module Main where

import Control.Monad (void)
import Language.LSP.Server qualified as LSP
import Server (server)

main :: IO ()
main = void (LSP.runServer server)
