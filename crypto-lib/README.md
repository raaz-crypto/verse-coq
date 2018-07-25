# The Verse low level crypto library.

The complete self contained source code of the verse _low level
cryptographic library_. The primary uses use case for this library is
to provide fast and correct implementations of cryptographic
primitives to the [`raaz`][raaz] cryptographic library. Hence, we do
not expect this library to be used as a standalone library. Even
rudimentary things like benchmarking and unit tests are meant to be
done by the [`raaz`][raaz] library.

Baring the files `libverse/verse.h` and `libverse/verse.c` all other C
and Assembly source code are infact generated from the Coq source
using the Verse eDSL. Therefore, any hacking is meant to be restricted
to editing these coq files.



## Compiling and Building

You can build a library archive via the command

```bash
make         # create the libverse.a archive
make tarball # create the source tarball.
```

Therefore, it is best to create a tarball and and dump it in the
source of your library or application. However, to test it we have
provided


A very minimal test "application" is defined in the file `main.c`
which can be compiled using the command

```bash
make TESTING=yes
```

There is nothing much that this application except linking errors.
The real tests are meant to be maintained with the [`raaz`][raaz]
library.

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

[raaz]: <https://github.com/raaz-crypt/raaz> "The Raaz cryptographic library"
