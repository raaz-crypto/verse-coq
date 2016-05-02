Require Vector.
Require BinNums.
Require Import Verse.Tactics.
Require Import NPeano.
Require BinNums.
(**

* Types in verse.

The assembly language supported by verse is typed. We have the
multi-word, array types and the type of sequences.

** Words.

The type [word n] denotes words of [2^n] bytes. A [vector m n] denotes
a vector of [2^m] words of size [2^n] bytes each.

** Vectors.

The type [vector n w] denotes
The type [word n] denotes words of [2^n] bytes. A [vector m n] denotes
a vector of [2^m] words of size [2^n] bytes each.

** Arrays.

Arrays are abstractions to contiguous memory locations in the machine
each of which can store a scalar.  Therefore, modification to the
contents of an array in a function changes the contents
globally. Arrays also required to specify the endianness of the values
as it matters when loading or storing into memory.

The dimensions of the arrays are fixed at compile time. Hence, they too
are bounded.

** Sequences.

Cryptographic primitives like block cipher often process a stream of
blocks or values. A sequence abstracts this. The stream type is
unbounded and its length is not known at compile time. As a result,
verse does not allow nested streams.

*)

Inductive value := Scalar | Vector.
Inductive bound :=
| Value : value -> bound
| Array
.

Inductive kind :=
| Bounded   : bound -> kind
| Unbounded : kind
.

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

(** Word types that are commonly found in machines *)

Definition Byte   := word 0. (** 2^0 = 1 byte *)
Definition Word8  := word 0. (** 2^0 = 1 byte *)
Definition Word16 := word 1. (** 2^1 = 2 byte *)
Definition Word32 := word 2. (** 2^2 = 4 byte *)
Definition Word64 := word 3. (** 2^3 = 8 byte *)

(* ** Common vector types

We have vector types of 128-bits and 256 bits given by
[Vector128_*] and [Vector256_*].

 *)

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

This module proves the correctness of the vector types defined

*)
Module VectorCorrectness.

  (**

      When you make a vector of 128-bits of word type n, you need to
      ensure that the total bits are of exactly 128 bits long. If you
      use vector k n, then this means that [2^k * 2^n = 128] or in
      other words [k + n = 4]. We prove these theorems here.

   *)

  Definition WFVector128 (v : type vectorK) : Prop
    := match v with
         | vector n (word m) => n + m = 4
         | _                 => False
       end.
  Definition WFVector256 (v : type vectorK) : Prop
    := match v with
         | vector n (word m) => n + m = 5
         | _                 => False
       end.

  Theorem v128_64WF : WFVector128 (Vector128_64).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v128_32WF : WFVector128 (Vector128_32).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v128_16WF : WFVector128 (Vector128_16).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v128_8WF : WFVector128 (Vector128_8).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v128_ByteWF : WFVector128 (Vector128Bytes).
  Proof.
    crush_inequalities.
  Qed.



  Theorem v256_64WF : WFVector256 (Vector256_64).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v256_32WF : WFVector256 (Vector256_32).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v256_16WF : WFVector256 (Vector256_16).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v256_8WF : WFVector256 (Vector256_8).
  Proof.
    crush_inequalities.
  Qed.

  Theorem v256_ByteWF : WFVector256 (Vector256Bytes).
  Proof.
    crush_inequalities.
  Qed.
End VectorCorrectness.
