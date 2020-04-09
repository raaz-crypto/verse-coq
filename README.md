Verse
=====

[![License: Apache-2.0][shields-license]][apache-2]
[![][ci-badge]][github-actions]

A domain specific language in coq used to write low-level
cryptographic primitives.

Configuring and installing
--------------------------

We recommend the use of opam2 for working with coq. For the exact
versions that are supported please see the current [build
status][travis-verse].


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
versions using which verse [is tested on our CI system][travis-verse].

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

Verse is an _Embedded Domain Specific Language_ (EDSL) where the
target code is represented as an inductive type in Coq. This EDSL is
use to implement actual primitives, the source of which are available
in the directory `src/Verse/CryptoLib`. The extracted low level code
is distributed as a separate library called [libverse], a library that
that can be embedded in other high level libraries. A snapshot of
[libverse] is built for this coq source using the helper scripts, and
makefile present in the directory `crypto-lib`.


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

[travis-verse]: <https://travis-ci.org/raaz-crypto/verse-coq/>
[libverse]: <https://github.com/raaz-crypto/libverse>
[shields-license]: <https://img.shields.io/badge/License-Apache--2.0-informational.svg>
[apache-2]: <http://www.apache.org/licenses/LICENSE-2.0> "Apache-2.0 license"

[ci-badge]: <https://github.com/raaz-crypto/verse-coq/workflows/CI/badge.svg> "Building source"
[github-actions]: <https://github.com/raaz-crypto/verse-coq/actions> "Github actions"
