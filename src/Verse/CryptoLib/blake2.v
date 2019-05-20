Require Import Verse.

Module Type CONFIG.

  (** The word size for the hash *)
  Parameter WORD_LOG_SIZE : nat.

  (** The number of rounds that is involved in hashing. *)
  Parameters ROUNDS : nat.

  (** The round constants for the hash *)
  Parameter IVVec : Vector.t (constant (word WORD_LOG_SIZE)) 8.

  (** The rotation constants used by the G function *)
  Parameter R0 R1 R2 R3 : nat.


End CONFIG.

(**

A single block of both sha512 and sha256 are 16-words in big endian
and the hash value is 8-words long.

*)

Definition HASH_SIZE : nat := 8.
Definition BLOCK_SIZE : nat := 16.
