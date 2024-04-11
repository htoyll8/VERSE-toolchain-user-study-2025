# The VERSE Development Toolchain

This repository assembles the core technologies that make up the VERSE TA1
toolchain and packages them into IDE and CI/CD integrations.

This is a companion to the [VERSE Open SUT
repository](https://github.com/GaloisInc/VERSE-OpenSUT) for TA2.

[ [VERSE project proposal](https://drive.google.com/drive/u/0/folders/1S6wk-aXLZh_dNGU0IcKxB2tnXe5zjV1C) ]

## Toolchain Components

The VERSE toolchain brings together core technologies from EPFL, the University
of Cambridge, the University of Illinois at Urbana-Champaign, the University of
Maryland, the University of Massachusetts Amherst, and the University of
Pennsylvania.

### CN

Developers write inline specifications alongside their C code using the CN
specification language. Additionally, CN's automated verification backend
attempts to automatically prove specifications.

[ [Homepage](https://www.cl.cam.ac.uk/~cp526/popl23.html),
[paper](https://www.cl.cam.ac.uk/~cp526/popl23.pdf),
[GitHub](https://github.com/rems-project/cerberus/tree/master/backend/cn),
[manual](https://github.com/rems-project/cerberus/tree/master/backend/cn/manual) ]

### Runtime Specification Testing

Runtime spec testing is made up of two parts:

1. Synthesizing test input from specifications, a form of property-based testing (PBT).
1. Transliterating CN specifications into C runtime tests that check whether the spec holds for a specific program execution.

TBD: Links and details as these projects progress.

See [Tyche](https://github.com/tyche-pbt/tyche-extension) and QuickChick ([manual](https://softwarefoundations.cis.upenn.edu/qc-current/index.html), [GitHub](https://github.com/QuickChick/QuickChick)) for inspiration.

### Proof Synthesis, Repair and Visualization

CN provides an escape hatch to Roq (formerly Coq) to provide manual proofs of properties that cannot be automatically verified.

- **Proof synthesis** attempts to automatically discharge these proof obligations.
- **Proof repair** attempts to automatically fix existing proofs if the code
  associated with them changes.
- **Proof visualization** assists the manual proof effort by tracking and
  visualizing complex C memory states and other proof details.

TBD: Links to project pages, more details as we discover them.

## Installation and Use

To be filled in as the toolchain is developed.

### How to run CN

You need (1) `git` and (2) `docker` (or a comparable alternative such as `colima`).

In the root directory invoke `make`.

## How to Contribute

- Review the [code of conduct](CONDUCT.md) and [developer guidelines](CONTRIBUTING.md).
- Check out the [reading list](docs/reading_list.md).
- Get some experience running CN on [simple examples](cn-intro).
