#!/bin/bash 

# Check if a filename was provided
if [ -z "$1" ]; then
  echo "Usage: $0 <filename>"
  exit 1
fi

# Construct the html debug file 
base_name=$(basename "$1" .c)
output_file="${base_name}.html"

echo "$1" | \
  entr -c ../cn/cn \
    --slow-smt=1 \
    --state-file="./${output_file}" \
    "$1"