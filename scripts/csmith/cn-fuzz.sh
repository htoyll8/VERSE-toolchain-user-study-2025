#!/bin/bash

csmith_params="--nomain --no-float --no-arrays"

maxattempts=10000
maxexamples=10
timestamp=$(date +%Y%m%d%H%M%S)

# Create a temporary file
mktmpfile=$(mktemp creduce_tmp.XXXXXX)
tmpfile="${mktmpfile}.c"
mv "$mktmpfile" "$tmpfile"
# Delete the file on exit 
trap "rm -f '$tmpfile'" EXIT

# The exit code of interest 
code=125

# creduce doesn't allow arguments to the 'interestingness test'. We get around
# this by setting env vars holding the file location and exit code 
export CREDUCE_TARGET_FILE="${tmpfile}"
export CREDUCE_TARGET_CODE=$code

# iteration variables 
attempts=0
examples=0

# Create the examples directory if it doesn't already exist 
mkdir ./examples 

printf "Searching "

while [[ $attempts -lt $maxattempts ]] && [[ $examples -lt $maxexamples ]]; do
  # Generate the test file 
  csmith $csmith_params > "${tmpfile}"
  # Override the csmith.h library 
  # TODO: might want to make this cleverer 
  sed -i '' 's/#include "csmith.h"/#include <stdint.h>/g' "${tmpfile}"

  # Test whether the file passes the interestingness test
  if sh ./cn-fuzz-test.sh; then
    printf "X"

    # Copy the file 
    copyname="${timestamp}_${examples}"
    cp "${tmpfile}" "./examples/${copyname}_original.c"

    # Reduce the file 
    creduce --tidy cn-fuzz-test.sh "${tmpfile}" >/dev/null 2>&1

    # Copy the result 
    cp "${tmpfile}" "./examples/${copyname}_reduced.c"

    ((examples++))
  else 
    printf "."
  fi
  ((attempts++))
done
