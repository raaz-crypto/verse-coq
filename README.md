Verse
=====

[![License: Apache-2.0][shields-license]][apache-2]
[![Build Staus][travis-status]][travis-raaz]

A domain specific language in coq used to write low-level
cryptographic primitives.

Configuring and installing
--------------------------

Verse has been tested with coq versions 8.6 and 8.7. It also required
the coq-color library. It is best to use opam to build the project.

## Setting up the coq environment.

We assume that you are using opam-2 in which case you need to
initialise it with the `--disable-sandboxing` option. Otherwise the
package coq-color used by verse will not compile.


```bash
opam init  --disable-sandboxing  --compiler "$OCAML_VER"
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
```

You will now need to get a version of coq. Select one of the coq
versions for which verse is tested (8.6 or 8.7).

```
opam install coq."$COQ_VER"
opam pin add coq "$COQ_VER"
opam install coq-color
```

Finally prepare the opam environment, configure, and then make.

```
eval $(opam config env) # set up opam environment if needed.
./configure.sh
make

```

Programming in Verse
--------------------

Verse is an _Embedded Domain Specific Language_ and as such generates
the assembly language code as a Coq inductive type. Here is a tiny example
which takes an array of 16-bit words and sets it to zero.

```coq

Require Import Verse.


Section ZeroBuffer.

  (* Paramterise over program variables *)
  Variable v   : VariableT.
  Arguments v [k] _.

  (* The buffer argument *)
  Variable buf : v (Array 10 bigE Word16).

  (* Define what variables are paramters, what are local variables on
    stack and what are allocated in registers *)

  Definition parameters : Declaration := [Var buf].
  Definition stack      : Declaration := [].
  Definition registers  : Declaration := [].

  (* Zero the ith entry of the buffer *)
  Definition  zeroIt (i : nat) (pf : i < 10) : code v.
    verse [ buf[- i -] ::== Ox "0000" ].
  Defined.

  (* Loop over all the indices of buffer *)
  Definition zeroBuf : code v := foreach (indices buf) zeroIt.

End ZeroBuffer.

```

See the directory Verse/Artifact/ for more examples.


Extraction of code
-------------------

In the example above, we wrote a simple verse program. To get actual code
targeting a real machine, we need to compile for a given architecture. Here
we illustrate the use of portable C as the architecture.

```coq
Require Import Verse.Arch.C.

Definition code : Doc + {Compile.CompileError}.
  Compile.function "zeroblocks" parameters stack registers.
  assignRegisters (--).
  statements zeroBuf.
Defined.
```

Now that we have compiled the above verse program into the coq
variable `code`.  The recommended way to get a string representation
of the program is to export it to ocaml and print it. This is achieved
as follows.

```coq
(* Extracting the code

*)

Require Import Verse.Extraction.Ocaml.

Definition main : unit := print_code code.
Recursive Extraction main.
```

We can then pipe the extracted code through the ocaml interpreter to
get the actual code.

```bash
 coqc src/Verse/TestCode/TestCode.v -R src Verse | ocaml -stdin
```

# A bigger example: libverse

A larger example for actual extracted code is [libverse], a small
low-level cryptographic library primarily meant for being embedded in
other high level libraries. All the primitives in [libverse] are
implemented in [verse][repo], the coq source for which resides in the
sub-directory `src/Verse/CryptoLib`. A snapshot of [libverse] is built
for this coq source using the helper scripts, and makefile present in
the directory `crypto-lib`.


# Legal

Copyright 2018, Piyush P Kurur

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

SPDX-License-Identifier: Apache-2.0


[wiki]: <https://github.com/raaz-crypto/verse-coq/wiki> "Verse coq repo"
[repo]: <https://github.com/raaz-crypto/verse-coq> "Verse on github"

[emailgroups]: <https://groups.google.com/forum/#!forum/hraaz> "Raaz on Google groups"

[travis-status]: <https://secure.travis-ci.org/raaz-crypto/verse-coq.png> "Build status"

[travis-raaz]: <https://travis-ci.org/raaz-crypto/verse-coq/>
[libverse]: <https://github.com/raaz-crypto/libverse>
[shields-license]: <https://img.shields.io/badge/License-Apache--2.0-informational.svg>
[apache-2]: <http://www.apache.org/licenses/LICENSE-2.0> "Apache-2.0 license"
