# Building and Running

This application should be buildable with `cabal` version 3.10.3.0 and `ghc`
version 9.6.4. The easiest way to install these tools locally is via
[GHCup](https://www.haskell.org/ghcup/).

- Run `install.sh`
  - This should put a server executable at `bin/cn-lsp-server`, which is where
    the debugging harness ([`bin/debug-server`](bin/debug-server)) expects to
    find it

If that succeeds, running the client should automatically start the server as a
child process.

The server requires a `cn` executable be available, and will fail to start
without one. If the environment variable `CN` is set, the server will treat its
contents as the path to a `cn` executable. If `CN` isn't set, it will look for
the first thing named `cn` on the user's `PATH`.
