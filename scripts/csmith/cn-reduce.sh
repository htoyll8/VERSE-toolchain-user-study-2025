#!/bin/bash

# A script that reduces CN testcases 
target_file=$1

# Capture the exit code of interest 
timeout 60 cn -I "$csmith_runtime" "$target_file" >/dev/null 2>&1
code=$?

echo "CN return code: ${code}"

# creduce doesn't allow arguments to the 'interestingness test' script. We get
# around this by setting env vars holding the file location and target exit code 
export CREDUCE_TARGET_FILE="${target_file}"
export CREDUCE_TARGET_CODE=$code

creduce cn-fuzz-helper.sh "${target_file}"