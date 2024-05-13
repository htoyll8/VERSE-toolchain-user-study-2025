#!/bin/bash

# Helper script for creduce with CN 

if [ -z "$CREDUCE_TARGET_FILE" ]; then
    echo "CREDUCE_TARGET_FILE is not set. Exiting with failure."
    exit 1
fi
if [ -z "$CREDUCE_TARGET_CODE" ]; then
    echo "CREDUCE_TARGET_CODE is not set. Exiting with failure."
    exit 1
fi

target_file=$CREDUCE_TARGET_FILE
code=$CREDUCE_TARGET_CODE

if [ -z "$CSMITH_RUNTIME" ]; then
  csmith_runtime=""
else 
  csmith_runtime=$CSMITH_RUNTIME
fi

# Compile the program
if ! gcc -I "$csmith_runtime" -c "$target_file" -o /dev/null >/dev/null 2>&1; then
  exit 1
fi

# Run CN on the compiled program, with a timeout
timeout 60 cn -I "$csmith_runtime" "$target_file" >/dev/null 2>&1
cn_status=$?

# Check the exit status
if [ $cn_status -eq $code ]; then
  # echo "Correct exit code" 
  exit 0
else
  # echo "Wrong exit code: ${cn_status}" 
  exit 1
fi
