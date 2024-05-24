{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Handlers.TextDocument.DidSave where

import Data.Aeson.Text qualified as Aeson
import Data.Text.Lazy qualified as Text
import Language.LSP.Protocol.Message (Method (..), SMethod (..), TNotificationMessage (..))
import Language.LSP.Protocol.Types (DidSaveTextDocumentParams)
import Language.LSP.Server (Handlers, notificationHandler)
import Log (sDebug)
import Monad (ServerM)

handler :: Handlers ServerM
handler = notificationHandler SMethod_TextDocumentDidSave doDidSave

doDidSave ::
  TNotificationMessage 'Method_TextDocumentDidSave ->
  ServerM ()
doDidSave notif =
  do
    sDebug $ Text.toStrict (Aeson.encodeToLazyText params)
  where
    params :: DidSaveTextDocumentParams
    params = notif._params
