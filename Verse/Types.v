(**

* Types in verse.

Most cryptographic primitives use datatypes that are relatively
simple.  In verse, we have

1. The word types. Word types are bounded in size in that the size
   required to store them is know.

2. Arrays of word types: Arrays are also bounded as their length
   necessarily have to be a constant. Arrays are the only means for
   accessing the main memory in verse and should be of a fixed
   dimension. They are contiguous locations of basic word types. To
   avoid endian confusion while loading and storing, they also need to
   specify the endianness.


3. A sequence of bound types. Often we need to process a stream of
   inputs each of which are bounded. A sequence type is for this
   purpose. Verse forbids nested sequences as sequences are unbounded.

*)


Inductive endian : Type := bigE | littleE | hostE.

(** The abstract syntax of verse types *)
Inductive type : Type :=
  | word       : nat  -> type
  | array      : nat  -> endian -> type -> type
  | sequence   : type -> type.


(**

Not all types are valid. The next

 *)

Definition Word8  : type := word 8.
Definition Byte   : type := Word8.
Definition Word16 : type := word 16.
Definition Word32 : type := word 32.

Module Properties.

Inductive Scalar : type -> Prop :=
  | ScalarWord {n : nat} : Scalar (word n).

Inductive Bounded          : type -> Prop :=
  | BoundedScalar {t : type}: Scalar t -> Bounded t
  | BoundedArray  {n : nat }
                  {t : type}
                  {e : endian}
    : Scalar t -> Bounded (array n e t).

Inductive WellFormed      : type -> Prop :=
  | WFBound    {t : type} : Bounded t -> WellFormed t
  | WFSeq      {t : type} : Bounded t -> WellFormed (sequence t).

End Properties.

(**

Some common types.

 *)

(**

Proving well formedness of types can be bothersome. This module
exposes some tactics to automatically dispose of some of these
obligations.

*)

Module Tactics.

  (**

 This tactic simplifies all type obligations.

   *)

  Import Properties.

  Ltac discharge_scalar_obligations := exact ScalarWord.

  Ltac discharge_bounded_obligations :=
    match goal with
      | [ |- Bounded (array _ _ _) ] =>
        apply BoundedArray; discharge_scalar_obligations
      | _
        => apply BoundedScalar; discharge_scalar_obligations
    end.


  Ltac discharge_wf_obligations :=
    match goal with
      | [ |- WellFormed (sequence _) ] =>
        apply WFSeq; discharge_bounded_obligations
      | _
        => apply WFBound; discharge_bounded_obligations
    end.

  Ltac types :=
    match goal with
      | [ |- context[ Scalar  _] ]
        => compute;  discharge_scalar_obligations
      | [ |- context[ Bounded _] ]
        => compute;  discharge_bounded_obligations
      | [ |- context[ WellFormed _]]
        => compute; discharge_wf_obligations
    end.

End Tactics.
