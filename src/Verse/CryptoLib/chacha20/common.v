(**

Definitions that are common to all chacha20 implementations. We expect
the following three variants of chacha20.

- An iterator that encrypts using the chacha20 cipher

- The HChaCha20 "hash" and the iterator for the xchacha20 cipher.

- A host endian variant of chacha20 keystream for use in csprg.


*)

Require Import Verse.

(**

First we define the underlying word type for the chacha20 primitive.

*)

Definition Word    := Word32.

(** ** Block

The block type is parameterised over the endianness as we need both
the standard little endian variant for the cipher and the host-endian
variant for use in the csprg.

*)

Definition BLOCK_SIZE := 16.
Definition KEY_SIZE   := 8.
Definition IV_SIZE    := 3.

Definition Block e := Array BLOCK_SIZE e Word.
Definition Key     := Array KEY_SIZE hostE Word.
Definition Counter := Word.
Definition IV   := Array IV_SIZE hostE Word.

(** ** Constants

Finally we have the constants that are used in the chacha20
algorithms.

*)

Definition C0 : constant Word := Ox "61:70:78:65".
Definition C1 : constant Word := Ox "33:20:64:6e".
Definition C2 : constant Word := Ox "79:62:2d:32".
Definition C3 : constant Word := Ox "6b:20:65:74".
