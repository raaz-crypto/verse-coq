(** printing sigma  %$\sigma$%   #σ#  *)
(** printing sigma0 %$\sigma_0$% #σ<sub>0</sub># *)
(** printing sigma1 %$\sigma_1$% #σ<sub>1</sub># *)

(** printing Sigma  %$\Sigma$%   #Σ#  *)
(** printing Sigma0 %$\Sigma_0$% #Σ<sub>0</sub># *)
(** printing Sigma1 %$\Sigma_1$% #Σ<sub>1</sub># *)
(** printing oplus  %$\oplus$%   #⊕#  *)

Require Import Verse.

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
  Parameter KVec : Vector.t (const (word WordSize)) ROUNDS.

  (** ** The sigma functions.

   Both sha512 and sha256 uses the functions [Sigma0], [Sigma1],
   [sigma0], and [sigma_1] defined as follows

   [ Sigma0(x) = RotR(x,R00) oplus RotR (x,R01) oplus RotR(x,R02) ]

   [ Sigma1(x) = RotR(x,R10) oplus RotR (x,R11) oplus RotR(x,R12) ]

   [ sigma0(x) = RotR(x,r10) oplus RotR (x,r11) oplus ShiftR(x,S12) ]

   [ sigma1(x) = RotR(x,r10) oplus RotR (x,r11) oplus ShiftR(x,S12) ]

   *)

  (**

   While the [Sigma0] and [Sigma1] are used in the message schedule,
   the functions [sigma0] and [sigma1] are used in the transformation
   of the hash state.  We parametrise these functions via the rotation
   and shift offsets.

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
