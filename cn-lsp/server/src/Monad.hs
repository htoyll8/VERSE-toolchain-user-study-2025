module Monad where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Reader.Class (MonadReader, asks)
import Language.LSP.Server (LanguageContextEnv, LspM, MonadLsp (..), runLspT)

type Config = ()

data ServerEnv = ServerEnv
  { seCtxEnv :: LanguageContextEnv Config,
    seLogFile :: FilePath
  }

newtype ServerM a = ServerM {unServerM :: ReaderT ServerEnv (LspM Config) a}
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadIO,
      MonadReader ServerEnv,
      MonadUnliftIO
    )

instance MonadLsp Config ServerM where
  getLspEnv = asks seCtxEnv

runServerM :: ServerEnv -> ServerM a -> IO a
runServerM serverEnv (ServerM rdrAction) =
  let lspAction = runReaderT rdrAction serverEnv
   in runLspT (seCtxEnv serverEnv) lspAction
