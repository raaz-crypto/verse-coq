Require Vector.
Require Import Verse.Tactics.

(**

* Types in verse.

The assembly language supported by verse is typed. We have the
multi-word, array types and the type of sequences.

** Words and vectors.

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

Inductive kind :=
| bounded   : nat -> kind
| unbounded : kind
.

Definition value := bounded 0.
(** The abstract syntax is specified in this module *)
Inductive type       : kind -> Type :=
| vector             : nat -> nat  -> type value
| array    (n : nat) : endian
                       -> type value
                       -> type (bounded n)
| sequence {n : nat} : type (bounded n)      -> type unbounded
with endian : Type := bigE  | littleE | hostE.

(** A constant of a given type *)
Inductive constant  : type value -> Type :=
| const {m n : nat} : Vector.t nat m -> constant (vector m n).

(** Some common types **)
Definition word   := vector 0.
Definition Byte   := word 0. (** 2^0 = 1 byte *)
Definition Word8  := word 0. (** 2^0 = 1 byte *)
Definition Word16 := word 1. (** 2^1 = 2 byte *)
Definition Word32 := word 2. (** 2^2 = 4 byte *)
Definition Word64 := word 3. (** 2^3 = 8 byte *)

Definition valuetype := type (bounded 0).

Ltac makeArray n e t :=
  match n with
    | 0 => fail 1 "array of length 0 defined"
    | _ => exact (array n e t)
  end.

Definition bigEndian (n : nat)(t : type (bounded 0))
  := array n bigE t.

Definition littleEndian (n : nat)(t : type (bounded 0))
  := array n littleE t.