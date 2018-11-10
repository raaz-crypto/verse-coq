Require Import Verse.
Require Vector.
Import VectorNotations.
Delimit Scope vector_scope with vector.

(** * SHA-2 hashes

The two hashes SHA512 and SHA256 have very similar structure defering
only in some parameters. We take advantage on the eDSL nature of verse
to share as much code as possible between the two implementation. This
code is parameterised by the following module type.


 *)

Module Type CONFIG.

  (** The size of the word type for the hash *)
  Parameter WordSize : nat.

  (** The number of rounds that is involved in hashing. *)
  Parameters ROUNDS : nat.

  (** The round constants for the hash *)
  Parameter KVec : Vector.t (constant (word WordSize)) ROUNDS.

  (** ** The sigma functions.

   Both sha512 and sha256 uses the functions Σ₀, Σ₁, σ₀, and σ₁
   defined as follows

   [ Σ₀(x) = RotR(x,R00) ⊕ RotR (x,R01) ⊕ RotR(x,R02) ]

   [ Σ₁(x) = RotR(x,R10) ⊕ RotR (x,R11) ⊕ RotR(x,R12) ]

   [ σ₀(x) = RotR(x,r10) ⊕ RotR (x,r11) ⊕ ShiftR(x,S12) ]

   [ σ₁(x) = RotR(x,r10) ⊕ RotR (x,r11) ⊕ ShiftR(x,S12) ]

   *)

  (**

   While the Σ₀ and Σ₁ are used in the message schedule, the functions
   σ₀ and σ₁ are used in the transformation of the hash state.  We
   parametrise these functions via the rotation and shift offsets.

   *)


  Parameter R00 R01 R02 : nat.
  Parameter R10 R11 R12 : nat.
  Parameter r00 r01 s0  : nat.
  Parameter r10 r11 s1  : nat.

  (** Notice that the functions are invariant under the permutation of
     the rotation offsets. However, assuming these additional
     constraints on these offsets, helps us give efficient
     implementations; we can optimise them for number of temporary
     variables.

   *)

  Parameter increasing_R's :
    R00 <= R01 <= R02 /\ R10 <= R11 <= R12.
  Parameter increasing_r's :
    r00 <= r01 /\ r10 <= r11.


End CONFIG.

(**

A single block of both sha512 and sha256 are 16-words in big endian
and the hash value is 8-words long.

*)

Definition HASH_SIZE : nat := 8.
Definition BLOCK_SIZE : nat := 16.
