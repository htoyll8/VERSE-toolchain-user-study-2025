module Monad where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Control.Monad.Reader (MonadReader, ReaderT (runReaderT))
import Language.LSP.Server (LanguageContextEnv, LspM, runLspT)

type Config = ()

data ServerEnv = ServerEnv
  { seCtxEnv :: LanguageContextEnv Config
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

runServerM :: ServerEnv -> ServerM a -> IO a
runServerM serverEnv (ServerM rdrAction) =
  let lspAction = runReaderT rdrAction serverEnv
   in runLspT (seCtxEnv serverEnv) lspAction
