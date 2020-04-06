# Extraction of libverse

This directory contains helper files that make extraction of the
source of [libverse] from the Coq source files.

All you need is a simple make. This will

1. Clone the version of libverse from github as a subdirectory if
   there is no such subdirectory. There are some hand written parts of
   libverse (like the verse.c and verse.h files).

2. Compile the verse library.

3. Extract the actual primitives into the libverse subdirectory.

## Workflow for releasing.

If you intend to release it would be better to start of by cloning
libverse from github using the ssh repo. This needs to be done only
once

On adding new cryptographic primitives, or some change in the code
generation module, the files generated in the `libverse` subdirectory
would be different from what is currently available in libverse. At
this point it might make sense to have a new release. Move into the
libverse directory and commit stuff that you want to include in the
release. Then push it to origin. Of course this will only work if you
have permissions to `git@github.com:raaz-crypto/libverse.git`.


[libverse]: <https://github.com/raaz-crypto/libverse>
