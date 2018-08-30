Require Import Verse.
Require Vector.
Import VectorNotations.
Delimit Scope vector_scope with vector.

(**

This module contains the common code fragment that is required by two
hashes SHA256 and SHA512.

 *)

Definition HASH_SIZE : nat := 8.
Definition BLOCK_SIZE : nat := 16.

Module Type CONFIG.

  (** The word type for the hash *)
  Parameter Word : type direct.

  (** The number of rounds _minus 1_ that is involved in hashing. The
      _minus 1_ while slightly unnatural, makes subsequent code quite
      convenient.  *)
  Parameters ROUNDS : nat.

  (** The round constants for the hash *)
  Parameter KVec : Vector.t (constant Word) (S ROUNDS).

End CONFIG.
