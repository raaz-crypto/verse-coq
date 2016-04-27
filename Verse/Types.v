Require Import Verse.Tactics.

(**

* Types in verse.

The assembly language supported by verse is typed. We have the word
type, array types and the type of sequences.

** Words.

The type [word n] denotes [n] byte long words. Word types are also
called scalars. They are also bounded in the sense that the memory
used is fixed at compilation time.

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

(** The abstract syntax is specified in this module *)
Inductive typeS : Type :=
| word       : nat  -> typeS         (** word n is words of n bytes *)
| array      : nat  -> endian -> typeS -> typeS
| sequence   : typeS -> typeS

with endian : Type := bigE | littleE | hostE.

(**

Not all elements expressed by typeS are valid. We now formulate
properties which assert various well formedness properties for types.

*)

(** Asserts that a type is a value type *)
Inductive Value : typeS -> Prop :=
| WordIsValue {n : nat} : Value (word n).

(** Asserts that a type is bounded      *)
Inductive Bounded : typeS -> Prop :=
| ValueIsBounded {t : typeS} :  Value t -> Bounded t
| ArrayIsBounded {n : nat}{e : endian}{s : typeS}
  : Value s -> Bounded (array n e s).

Inductive Wellformed  : typeS -> Prop :=
| BoundedIsWellformed  {t : typeS} : Bounded t -> Wellformed t
| SequenceIsWellformed {t : typeS} : Bounded t -> Wellformed (sequence t)
.

Definition type (P : typeS -> Prop) := { t : typeS | P t }.
Definition wellformedType := type Wellformed.
Definition valueType      := type Value.
Definition boundedType    := type Bounded.


Ltac strengthen :=
  match goal with
    | [ |- Bounded ?T ]
      => apply ValueIsBounded; assumption
    | [ |- Wellformed ?T ]
      => apply BoundedIsWellformed; first [ assumption | strengthen ]
  end.
