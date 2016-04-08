(**

* Types in verse.

Most cryptographic primitives use datatypes that are relatively
simple.  In verse, we have

1. Word types.

2. Array types

3. Sequence types.

*)


Require Import Verse.Tactics.

Inductive endian : Type := bigE | littleE | hostE.


(** The abstract syntax of verse types *)

Inductive type : Type :=
  | word       : nat  -> type
  | array      : nat  -> endian -> type -> type
  | sequence   : type -> type.

(**

Some common types are defined below.

 *)

Definition Word8  : type := word 8.
Definition Byte   : type := Word8.
Definition Word16 : type := word 16.
Definition Word32 : type := word 32.

(** ** Properties of types.

This module contains various properties of types.


*)

Module Properties.

(** Propertie asserting that a given type is a scalar *)
Inductive Scalar : type -> Prop :=
  | ScalarWord {n : nat} : Scalar (word n).

(** Property asserting that a given type is a vector *)
Inductive Bounded          : type -> Prop :=
  | BoundedScalar {t : type}: Scalar t -> Bounded t
  | BoundedArray  {n : nat }
                  {t : type}
                  {e : endian}
    : Scalar t -> Bounded (array n e t).

(** Property asserting that a given type is well formed *)
Inductive WellFormed      : type -> Prop :=
  | WFBound    {t : type} : Bounded t -> WellFormed t
  | WFSeq      {t : type} : Bounded t -> WellFormed (sequence t).

End Properties.

(**

** Type tactics.

Often during proof developement, we need to prove various properties
about types. The tactics [scalar], [bounded] and [wellformed] are
precisely for this. The tactics [types] is a generic tactic that
proves all the above properties.


Often we only want to ensure that a type has a given property; the
[ensure_]family of tactics are for this purpose. Like the tactic
[ensure], these tactic do not leave the associated assertions in the
hypothesis. They are mostly for asserting property and moving on.


*)

Module Tactics.
  Import Properties.

  (** Proves that a type is a scalar *)

  Ltac scalar :=
    idtac;(* For some mysterious reason idtac is required *)
    match goal with
      | [ |- context[Scalar (word _)] ] => exact ScalarWord
      | [ |- context[Scalar _] ]        => compute; scalar
      | _                               => fail 0 "scalar type"
    end.

  (** Proves that a type is bounded *)

  Ltac bounded :=
    idtac; (* For some mysterious reason idtac is required *)
    match goal with
      | [ |- Bounded (array _ _ _) ]
        => apply BoundedArray; scalar
      | [ |- Bounded (word _)      ]
        => apply BoundedScalar; scalar
      | [ |- Bounded _ ] => compute ; bounded
      | _ => fail 1 "bounded type"
    end.

  (** Proves that a type is well formed *)
  Ltac wellformed :=
    idtac;(* For some mysterious reason idtac is required *)
    match goal with
      | [ |- WellFormed (sequence _) ] => apply WFSeq; bounded
      | [ |- WellFormed (array _ _ _)] => apply WFBound; bounded
      | [ |- WellFormed (word  _)    ] => apply WFBound; bounded
      | [ |- WellFormed _           ] => compute ; wellformed
      | _                              => fail 1 "wellformed type"
    end.

  (** Proves all properties about goals *)
  Ltac types :=
    idtac;(* For some mysterious reason idtac is required *)
    match goal with
      (*| [ ?S : type, ?T : type |- context[ S = T] ] => idtac*)
      | [ |- context[ Scalar  _] ]
        => scalar
      | [ |- context[ Bounded _] ]
        => bounded
      | [ |- context[ WellFormed _]]
        => wellformed
    end.

  (**

   *)

  Ltac ensure_scalar  t    := ensure (Scalar     t) scalar.
  Ltac ensure_bounded t    := ensure (Bounded    t) bounded.
  Ltac ensure_wellformed t := ensure (WellFormed t) wellformed.

End Tactics.
