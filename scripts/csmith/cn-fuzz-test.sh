#!/bin/bash

if [ -z "$CREDUCE_TARGET_FILE" ]; then
    echo "CREDUCE_TARGET_FILE is not set. Exiting with failure."
    exit 1
fi
if [ -z "$CREDUCE_TARGET_CODE" ]; then
    echo "CREDUCE_TARGET_CODE is not set. Exiting with failure."
    exit 1
fi

file=$CREDUCE_TARGET_FILE
code=$CREDUCE_TARGET_CODE

# Compile the program
if ! gcc -c "$file" -o /dev/null >/dev/null 2>&1; then
  # echo "Compilation failed."
  exit 1
fi

# Run CN on the compiled program, with a timeout
timeout 60 cn "$file" >/dev/null 2>&1
cn_status=$?

# Check the exit status
if [ $cn_status -eq $code ]; then
  # echo "Correct exit code" 
  exit 0
else
  # echo "Wrong exit code: ${cn_status}" 
  exit 1
fi
