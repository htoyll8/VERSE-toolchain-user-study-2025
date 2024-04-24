#!/usr/bin/env bash

set -e

BIN_NAME=cn-lsp-server
INSTALL_DIR=bin

cabal build exe:$BIN_NAME

mkdir -p $INSTALL_DIR

cp $(cabal exec which $BIN_NAME) $INSTALL_DIR
