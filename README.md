Verse
=====

A domain specific language in coq used to write low-level
cryptographic primitives.

Building with multiple coq-versions
-----------------------------------

You need `opam` for building and testing the source code for multiple
versions of coq. You need to set the the environment variable $COQ_VER
and run the script `./scripts/opam-build.sh`. Here is an example.

```
COQ_VER=8.6 ./scripts/opam-build.sh init
COQ_VER=8.6 ./scripts/opam-build.sh build

```

[![Build Staus][travis-status]][travis-raaz]

[wiki]: <https://github.com/piyush-kurur/verse-coq/wiki> "Verse coq repo"
[repo]: <https://github.com/piyush-kurur/verse-coq> "Verse on github"

[emailgroups]: <https://groups.google.com/forum/#!forum/hraaz> "Raaz on Google groups"

[travis-status]: <https://secure.travis-ci.org/piyush-kurur/verse-coq.png> "Build status"

[travis-raaz]: <https://travis-ci.org/piyush-kurur/verse-coq/>
