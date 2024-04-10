# QuickChick

## Setup and Installation

You will need OCaml and its package manager `opam`: [installation instructions](https://ocaml.org/install).

QuickChick requires Coq, and the simplest way to install it is via `opam`:

```bash
opam pin coq 8.17.3
```

Note that we will stick to version `8.17.3` for now. The latest version `8.18` appears to have some issues
when invoking QuickChick from within Coq.

In case you get weird `opam` errors, you might first need set up your
shell's environment properly. In `bash`, this amounts to invoking `eval $(opam env)`. 

Next, we will install QuickChick itself, which requires adding another repository to `opam`: 
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quickchik
```

### Trying out QuickChick

As a quick test, you should now be able to invoke
```bash
quickChick --help
``` 
and get a reasonable help message from QuickChick.

Here is a small Coq example (nabbed from [Software Foundations](https://softwarefoundations.cis.upenn.edu/qc-current/index.html)):
```coq
From QuickChick Require Import QuickChick.
Require Import List ZArith. Import ListNotations.

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if h =? x then t else h :: remove x t
  end.

Conjecture removeP : forall x l,  ~ (In x (remove x l)).

QuickChick removeP.
```
Put it into a file, say `test.v`. Let's see if `remove` satisfies the `removeP` conjecture (spoiler: it doesn't),
by compiling the file with Coq:
```bash
coqc test.v
```
QuickChick will promptly find a counterexample:
```bash
QuickChecking removeP
3
[3; 3]
*** Failed after 4 tests and 0 shrinks. (0 discards)
Time Elapsed: 0.158599s
```
You are good to go. Enjoy QuickChick!

### Coq IDEs

You can find a list of IDEs/plugins on the official [Coq page](https://coq.inria.fr/user-interfaces.html).

**VSCode**

Since we have to restrict ourselves to Coq `8.17.3` for now (see above), you will need to install
the [legacy Coq extension](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1).

The [cutting edge version](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq) requires
at least Coq `8.18`. Note that it's worth looking into, since it is the first version of (Vs)Coq that
offers a full [language server protocol (LSP)](https://microsoft.github.io/language-server-protocol/) implementation.
We are considering to build our IDE around LSP.

## Learning Resources

* There is a [dedicated issue of Software Foundations](https://softwarefoundations.cis.upenn.edu/qc-current/index.html) on QuickChick!
The other books are also recommended if you need to acquire basic proficiency with Coq itself first.

* The official QuickChick [github](https://github.com/QuickChick/QuickChick) repo contains a fairly extensive set of 
[examples](https://github.com/QuickChick/QuickChick/tree/master/examples). Just invoke `make` in that folder to run them all!
