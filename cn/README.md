# CN

## Setup

### Pre-built Docker Container

Be sure to first invoke `make` in the parent directory.

### Compiling the Docker Container from Scratch

TODO

## Usage

### As Command-Line Tool

The `cn` script is a wrapper for the pre-built Docker container. 

Type `./cn <args>`, e.g., `./cn ./cerberus/tests/cn/memcpy.c`. 

For help, type `./cn --help`. 

You likely want to place the `cn` script somewhere in your `$PATH`.

TODO: Figure out the proof workflow with `cn`.

### As Virtual Machine

You can also work from within in the Docker container.

For example, within this directory you can execute the CN test suite as follows:

```bash
docker run -it --rm -v "$PWD":/data -w /data bracevac/cn /bin/bash
user1@efc6aa78f4c5:/data$ ./cerberus/tests/run-cn.sh
```

TODO: Move away from Docker hub and use Artifactory.


## Case Studies

Larger case studies can be found in `cn-pKVM-buddy-allocator-case-study/` and `CN-pKVM-early-allocator-case-study/`.
TODO: seem to be broken.
