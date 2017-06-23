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

(*
Inductive kind  := Unbounded | Bounded : bound -> kind
with      bound := Array     | Value   : value -> bound
with      value := Scalar    | Vector.

(** Some short cuts to kinds. *)
Definition valueK  (v : value) := Bounded (Value v).
Definition scalarK := valueK Scalar.
Definition vectorK := valueK Vector.
Definition arrayK  := Bounded Array.
 *)

(**

The inductive definition of types in verse.

*)

Inductive type       : Type :=
| word               : nat -> type                    (* 2^n bytes                              *)
| vector             : nat -> type -> type            (* vector type of 2^n individual elements *)
| array              : nat -> endian -> type -> type
| sequence           : type -> type
with endian : Type := bigE | littleE | hostE.

Inductive isValue : type ->  Prop :=
| wordIsValue        {n : nat} : isValue (word n)
| vectorIsValue      {n : nat}{t : type} :  isValue (vector n t)
.

Inductive isBounded : type -> Prop :=
| wordIsBounded      {n : nat} : isBounded (word n)
| vectorIsBounded    {n : nat}{t : type} : isBounded (vector n t)
| arrayIsBounded     {n : nat}{e : endian}{t : type} : isBounded (array n e t)
.

(**

* Size calculations.

The number of bytes required to represent an element of
a given type

*)
(*
Require Import NPeano.
Require Import Nat.

Fixpoint bytes {b : bound}(t : type (Bounded b)) : nat :=
  match t with
    | word   n       => 2^n
    | vector m w     => 2^m * bytes w
    | array  n _ v   => n   * bytes v
  end.

Definition bits {b : bound}(t : type (Bounded b)) : nat
  := 8 * bytes t.
*)
