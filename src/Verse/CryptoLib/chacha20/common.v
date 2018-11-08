Require Import Verse.
(** Types relevant to Chacha20

*)

Definition Word    := Word32.

(**

While ChaCha20 is defined on little endian, when using chacha20 as a
csprg we really do not care about the endianness. It therefore makes
sense to have a host endian variant which might be marginally faster
as well.

*)

Definition Block e := Array 16 e Word.
Definition Key     := Array 8 hostE Word.
Definition IV      := Array 3 hostE Word.
Definition Counter := Word.

(** Constants used in ChaCha20 *)

Definition C0 : constant Word := Ox "61:70:78:65".
Definition C1 : constant Word := Ox "33:20:64:6e".
Definition C2 : constant Word := Ox "79:62:2d:32".
Definition C3 : constant Word := Ox "6b:20:65:74".
