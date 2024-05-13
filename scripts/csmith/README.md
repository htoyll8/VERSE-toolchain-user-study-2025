This directory contains two scripts that try to find and reduce errors in CN: 

* `cn-reduce.sh` - a script that takes a file that causes CN to crash and uses
  `creduce` to generate a minimized crashing case. 

* `cn-fuzz.sh` - a script that uses `csmith` to find files that generate a
  particular CN error, and then uses `creduce` to minimize the error file. 

Both of these scripts depend on `test-with-cn.sh` which defines the
'interestingness test' for `creduce`. 


## `cn-reduce.sh` 

This script takes a program, runs CN on it, and then minimizes to a program that
compiles and generates the same exit code from CN. Mostly useful for error case
reduction. 

Call it as follows: 
``` 
$ sh ./cn-reduce.sh <target> 
```

NOTE: The file will be reduced destructively in place, but the original will be
copied to `<filename>.orig` in the same directory. 

## `cn-fuzz.sh`

This script generates small random programs that crash CN. Call the script as
follows: 
```
$ sh ./cn-fuzz.sh
``` 

Original and reduced files are stored in the subdirectory `examples`. This
directory will be created if it doesn't already exist. 

### Setup 

Before running the script, you must set the variable `csmith_runtime` to
identify where the `csmith` runtime libraries exist in your system. 

As an ugly hack, you must also modify `runtime/simple_math.h` to comment out all
floating point operations. There's undoubtedly a cleverer way to do this...
