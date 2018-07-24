# The Verse low level crypto library.

This directory contains the complete self contained source code the
verse _low level cryptographic library_. This library is *not* a
standalone cryptolibrary and is only meant to provide the
implementation of low level cryptographic primitives that can be
called other higher level libraries in C (or any other language that
supports FFI to C). The C and Assembly source code that comes with
library is not meant to be edited as the themselves are generated
using the Verse eDSL.

## Convention


Verse expose C function as well as assembly language functions for
various primitives. The source code is arranged according to the
following convention.

1. The function name that implement a primitive `p` for an
   architecture `a` making use of the processor features `f` will be
   names `verse_p_a_f`, e.g. `verse_chacha20_x86_64_avx2`. If there
   are multiple features that are required, it should be separated by
   `_` (underscores).

2. The above function will reside in the file `lib/p/a/f.ext`, where
   `ext` is either `c` if it is a portable C code or is 's' if it is
   in assembly language. The corresponding `Coq` source will be at
   `p/a/f.v`.

3. The generated source (C or assembly) will be at `lib/p/a/f.ext`


There might be other functions that are shared by multiple
implementations and primitives. These will be located conveniently in
the directory hierarchy somewhere.
