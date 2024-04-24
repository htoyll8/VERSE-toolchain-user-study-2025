# Building and Running

This application should be buildable with `cabal` version 3.10.3.0 and `ghc`
version 9.6.4. The easiest way to install these tools locally is via
[GHCup](https://www.haskell.org/ghcup/).

- Run `install.sh`
  - This should put a server executable at `bin/cn-lsp-server`, which is where
    the debugging harness ([`bin/debug-server`](bin/debug-server)) expects to
    find it
