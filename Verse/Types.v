Require Import String.
Require Import Verse.Tactics.
Require Import Verse.BinTree.
Require Import Verse.Nibble.
Require Import Verse.Error.
Require Import Verse.Types.Internal.

(** * Types in verse.

The verse EDSL supports the standard word types, vectors type, arrays
and sequences. The types exposed from this module is what users of
verse should stick to. There is more to types and all its gory details
of types are exposed from the module [Verse.Types.Internal].

*)

(** Standard word types/scalars *)
Definition Byte   : type := WordT 0.
Definition Word8  : type := WordT 0.
Definition Word16 : type := WordT 1.
Definition Word32 : type := WordT 2.
Definition Word64 : type := WordT 3.

(** Standard vector types *)
Definition Vector128_64   : type := VectorT 1 Word64.
Definition Vector128_32   : type := VectorT 2 Word32.
Definition Vector128_16   : type := VectorT 3 Word16.
Definition Vector128_8    : type := VectorT 4 Word8.
Definition Vector128Bytes : type := VectorT 4 Byte.

Definition Vector256_64   : type := VectorT 2 Word64.
Definition Vector256_32   : type := VectorT 3 Word32.
Definition Vector256_16   : type := VectorT 4 Word16.
Definition Vector256_8    : type := VectorT 5 Word8.
Definition Vector256Bytes : type := VectorT 5 Byte.

(**

* Constants.

For a value type [t], the type [constant t] denotes a Coq type that
represents a constant of type [t].

 *)

Inductive constant : type -> Type :=
| wconst {n : nat} : Bin nibble      (S n) -> constant (word n)
| vconst {n m : nat}
  : Bin (constant (word m)) n -> constant (vector n (word m))
.




(* begin hide *)
Module Parse.
  Definition parseW (n : nat)(s : string) :
    option (constant (word n)) :=
    match parse s with
      | None      => None
      | Some nibs => match @merge nibble (S n) nibs with
                       | None   => None
                       | Some b => Some (wconst b)
                     end
    end.

  Definition parseV (m n : nat)(lc : list (constant (word n)))
  : option (constant (vector m (word n))) :=
    match merge lc with
      | None   => None
      | Some b => Some (vconst b)
    end.
  Inductive ConstError := BadWord | BadVector.

End Parse.
Import Parse.


(** The expression [w n s] parses a [word n] constant form a string *)

Definition w (n   : nat)(s : string)
  := optionToError BadWord (parseW n s).

(** Create a vector constant from a list of values *)
Definition v (m  : nat){n : nat}(ls : list (constant (word n)))
  := optionToError BadVector (parseV m n ls).

(* end hide *)

(**

The constructors of [constant t] are not very convenient to use. We
given convenient combinators to build constants out of the base16
encoded string representations as follows.

- Using the combinators [w8], [w16], [w32], [w64] on a string
  of base16 characters of appropriate length.


*)

Definition w8  := w 0.
Definition w16 := w 1.
Definition w32 := w 2.
Definition w64 := w 3.

(**

- Using the [v128_*] and [v256_*] combinators on lists of
  appropriate word constants.

*)

Definition v128_64 := @v 1 3.
Definition v128_32 := @v 2 2.
Definition v128_16 := @v 3 1.
Definition v128_8  := @v 4 0.

Definition v256_64 := @v 2 3.
Definition v256_32 := @v 3 2.
Definition v256_16 := @v 4 1.
Definition v256_8  := @v 5 0.

(**

Given below are few examples of the usage of these combinators.

 *)


Import List.ListNotations.
Definition asciiA  : constant Word8 := w8 "41".
Definition a128Vector : constant Vector128_64
  := v128_64 [ w64 "0123456789ABCDEF"; w64 "0123456789ABCDEF"].

Definition aWord64 := w64 "FEDCBA9876543210".
Definition a256Vector : constant Vector256_64
  := v256_64 [ aWord64; aWord64; aWord64 ; w64 "0123456789ABCDEF"].

(**

** Errors at compile type.

The definition of the constant type and the combinators ensure that
certain length checks on the constants declared are done by the type
system of Coq. For example, string arguments supplied for the
combinator [w16] should be of length 4 and should containing only
valid hex characters. This helps in early detection of errors that
occur due to typos when transcribing algorithms.

*)





(* begin hide *)
(*
Module Correctness.

  Theorem w8_WF : bits Word8 = 8.
  Proof.
    trivial.
  Qed.

  Theorem w16_WF : bits Word16 = 16.
  Proof.
    trivial.
  Qed.

  Theorem w32_WF : bits Word32 = 32.
  Proof.
    trivial.
  Qed.

  Theorem w64_WF : bits Word64 = 64.
  Proof.
    trivial.
  Qed.

  Theorem v128_64WF : bits Vector128_64 = 128.
  Proof.
    trivial.
  Qed.

  Theorem v128_32WF :  bits Vector128_32 = 128.
  Proof.
    trivial.
  Qed.

  Theorem v128_16WF :  bits Vector128_16 = 128.
  Proof.
    trivial.
  Qed.

  Theorem v128_8WF :  bits Vector128_8 = 128.
  Proof.
    trivial.
  Qed.

  Theorem v128_ByteWF : bits Vector128Bytes = 128.
  Proof.
    trivial.
  Qed.

  Theorem v256_64WF :  bits Vector256_64 = 256.
  Proof.
    trivial.
  Qed.

  Theorem v256_32WF : bits Vector256_32 = 256.
  Proof.
    trivial.
  Qed.

  Theorem v256_16WF : bits Vector256_16 = 256.
  Proof.
    trivial.
  Qed.

  Theorem v256_8WF : bits Vector256_8 = 256.
  Proof.
    trivial.
  Qed.

  Theorem v256_ByteWF : bits Vector256Bytes = 256.
  Proof.
    trivial.
  Qed.
End Correctness.
*)
(* end hide *)
