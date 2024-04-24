module Server where

import Language.LSP.Server (type (<~>) (Iso))
import Language.LSP.Server qualified as LSP

server :: LSP.ServerDefinition ()
server =
  LSP.ServerDefinition
    { LSP.defaultConfig = (),
      LSP.configSection = mempty,
      LSP.parseConfig = \_ _ -> pure (),
      LSP.onConfigChange = \_ -> pure (),
      LSP.doInitialize = \_ _ -> pure (pure ()),
      LSP.staticHandlers = \_ -> mempty,
      LSP.interpretHandler = \_ -> Iso id id,
      LSP.options = LSP.defaultOptions
    }
