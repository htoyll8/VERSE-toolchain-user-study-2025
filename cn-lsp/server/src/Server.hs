{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Server where

import Control.Monad.IO.Class (liftIO)
import Data.Aeson (Value)
import Data.Text (Text)
import Language.LSP.Protocol.Message qualified as LSP
import Language.LSP.Protocol.Types qualified as LSP
import Language.LSP.Server (LanguageContextEnv, type (<~>) (Iso))
import Language.LSP.Server qualified as LSP
import Monad (Config, ServerEnv (..), ServerM, runServerM)

server :: LSP.ServerDefinition Config
server = LSP.ServerDefinition {..}
  where
    defaultConfig :: Config
    defaultConfig = ()

    configSection :: Text
    configSection = "CN"

    parseConfig :: Config -> Value -> Either Text Config
    parseConfig _ _ = Right ()

    onConfigChange :: Config -> ServerM ()
    onConfigChange _ = pure ()

    doInitialize ::
      LanguageContextEnv Config ->
      LSP.TRequestMessage 'LSP.Method_Initialize ->
      IO (Either LSP.ResponseError ServerEnv)
    doInitialize ctxEnv _ = pure (Right (ServerEnv {seCtxEnv = ctxEnv}))

    staticHandlers :: LSP.ClientCapabilities -> LSP.Handlers ServerM
    staticHandlers _ = mempty

    interpretHandler :: ServerEnv -> ServerM <~> IO
    interpretHandler serverEnv = Iso (runServerM serverEnv) liftIO

    options :: LSP.Options
    options = LSP.defaultOptions
