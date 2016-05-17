Require Import String.
Require Import Verse.Tactics.
Require Import Verse.BinTree.
Require Import Verse.Nibble.
Require Import Verse.Error.

(**

* Types in verse.

The assembly language supported by verse is typed. We have the
words, vectors, array types and the type of sequences.

** Values.

Verse supports both scalar values and vector values. The scalar types
that are supported are [Word8], [Word16], [Word32] and [Word64]. The
type [Byte] is an aliase for [Word8]. The libary also supports 128 and
256 vector types of each of the above type. For example,
[Vector128_64] denotes a vector that consists of 2 64-bit word where
as [Vector256_64] denotes the vector type that consists of 4 64-bit
words. These are the standard vector and word types supported and
users should use these in the code.

Internally, the value [word n] denotes scalar values that are unsigned
integers of [2^n] bytes. Vector of [2^m] elements, each of which are
of type [word n] are captured by the type [vector m (word n)].
However, users should stick to the standard vector and word types as
much as possible.

** Arrays.

Arrays are abstractions to contiguous memory locations in the machine
each of which can store a value. Arrays also required to specify the
endianness of the values as it matters when loading or storing into
memory.

** Sequences.

Cryptographic primitives like block cipher often process a stream of
blocks. A sequence type abstracts such streams of block. The number of
elements in a sequence is not know at compile time but its elements
are required to be a bounded type, i.e. either a value or an array
type.


** The kind system.

The type system has to rule out certain types like for example nested
sequences or vector of arrays etc. A rudimentary kind system is
implemented to avoid such errors. The kind system ensures the following
restrictions.

  - The type [vector t] is valid only for a scalar type [t], i.e. [t]
    is a word type.

  - The array of type [t] is valid if and only if the type [t] is a
    value.

  - The type [sequence t] is valid if and only if the type [t] is a
    bounded type, i.e. [t] is either an array or a value type.

 *)

Inductive kind  := Unbounded | Bounded : bound -> kind
with      bound := Array     | Value   : value -> bound
with      value := Scalar    | Vector
.


(** Some short cuts to kinds. *)
Definition valueK  (v : value) := Bounded (Value v).
Definition scalarK := valueK Scalar.
Definition vectorK := valueK Vector.
Definition arrayK  := Bounded Array.


(** The abstract syntax is specified in this module *)
Inductive type       : kind -> Type :=
| word               : nat -> type (Bounded (Value Scalar))
| vector             : nat
                     -> type (Bounded (Value Scalar))
                     -> type (Bounded (Value Vector))
| array (n : nat){v : value} : endian
                             -> type (Bounded (Value v))
                             -> type (Bounded Array)
| sequence {b : bound} : type (Bounded b) -> type Unbounded
with endian : Type := bigE  | littleE | hostE.


(**

* Size calculations.

The number of bytes required to represent an element of
a given type

*)

Require Import NPeano.

Fixpoint bytes {b : bound}(t : type (Bounded b)) : nat :=
  match t with
    | word   n        => 2^n
    | vector m w      => 2^m * bytes w
    | array  n _ _ v  => n   * bytes v
  end.

Definition bits {b : bound}(t : type (Bounded b)) : nat
  := 8 * bytes t.


Definition scalartype            := type scalarK.
Definition vectortype            := type vectorK.
Definition arraytype             := type arrayK.
Definition valuetype (v : value) := type (valueK v).


(** Standard word types/scalars *)
Definition Byte   := word 0.
Definition Word8  := word 0.
Definition Word16 := word 1.
Definition Word32 := word 2.
Definition Word64 := word 3.

(** Standard vector types *)
Definition Vector128_64   := vector 1 Word64.
Definition Vector128_32   := vector 2 Word32.
Definition Vector128_16   := vector 3 Word16.
Definition Vector128_8    := vector 4 Word8.
Definition Vector128Bytes := vector 4 Byte.

Definition Vector256_64   := vector 2 Word64.
Definition Vector256_32   := vector 3 Word32.
Definition Vector256_16   := vector 4 Word16.
Definition Vector256_8    := vector 5 Word8.
Definition Vector256Bytes := vector 5 Byte.




(**

  A constant of a given type. The constructors of this type
  is an eye sore. To create constatns use the functions [w]
  and [v] respectively.

*)

Inductive constant :
  forall {k : kind}, type k -> Type
  :=
| wconst {n : nat} : Bin nibble      (S n) -> constant (word n)
| vconst {n : nat}{ty : type (Bounded (Value Scalar))}
  : Bin (constant ty) n -> constant (vector n ty)
.

(* begin hide *)
Module Internal.
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

End Internal.
(* end hide *)

Import Internal.



(** The expression [w n s] parses a [word n] constant form a string *)

Definition w (n   : nat)(s : string)
  := optionToError BadWord (parseW n s).

(** Create a vector constant from a list of values *)
Definition v (m  : nat){n : nat}(ls : list (constant (word n)))
  := optionToError BadVector (parseV m n ls).



Definition w8  := w 0. (** hex string to Word8  *)
Definition w16 := w 1. (** hex string to Word16 *)
Definition w32 := w 2. (** hex string to Word32 *)
Definition w64 := w 3. (** hex string to Word64 *)


Definition v128_64 := @v 1 3. (** 2 x 64-bit vector constant *)
Definition v128_32 := @v 2 2. (** 4 x 32-bit vector constant *)
Definition v128_16 := @v 3 1. (** 8 x 16-bit vector constant *)
Definition v128_8  := @v 4 0. (** 16 x 8-bit vector constant *)


Definition v256_64 := @v 2 3. (** 4  x 64-bit vector constant *)
Definition v256_32 := @v 3 2. (** 8  x 32-bit vector constant *)
Definition v256_16 := @v 4 1. (** 16 x 16-bit vector constant *)
Definition v256_8  := @v 5 0. (** 32 x 8-bit vector constant  *)


(* begin hide *)

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
(* end hide *)
