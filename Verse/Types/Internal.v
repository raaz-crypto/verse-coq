Require Import Verse.Error.
(** * Types in Verse.

Given below is the inductive type that captures data types used in the
verse EDSL.

*)
Inductive type       : Type :=
| word               : nat -> type                    (* 2^n bytes                              *)
| vector             : nat -> type -> type            (* vector type of 2^n individual elements *)
| array              : nat -> endian -> type -> type
| sequence           : type -> type
with endian : Type := bigE | littleE | hostE.

(** ** Well formed types

There are some restrictions on the type that can be used
in actual programs. For example, one can define vectors only of word
types, arrays cannot be defined on anything but vectors or word. We
provide the combinators [WordT], [VectorT], [ArrayT], and [SequenceT],
which are the smart variants of the constructors [word], [vector],
[array], and [sequence] respectively, which also ensures that the type
thus constructed are all well formed.

*)

Inductive BadType : Prop := BadVector | BadArray | BadSequence.

(* begin hide *)


(* end hide *)

(** Checks the well formedness of the type *)
Fixpoint typeCheck (ty : type) : type + {BadType}
  :=
  match ty with
  | word _                   => inleft ty
  | vector m (word n)        => inleft ty
  | vector _ _               => inright BadVector
  | array  _ _ (sequence _)  => inright BadArray
  | array  _ _ (array _ _ _) => inright BadArray
  | array  m e typ           => ap (array m e) (typeCheck typ)
  | sequence (sequence _)    => inright BadSequence
  | sequence typ             =>  ap sequence (typeCheck typ)
  end.

(** Makes type smartly, i.e. typeCheck and recover the type *)
Definition maketype (ty : type)                        := recover (typeCheck ty).



(** Same as word for consistency with other smart constructors *)
Definition WordT    n                                  := word n.

(** Smart variant of the constructor [vector] *)
Definition VectorT  (n : nat) (ty : type)              := maketype (vector n ty).

(** Smart variant of the constructor [array] *)
Definition ArrayT   (n : nat) (e : endian) (ty : type) := maketype (array n e ty).

(** Smart variant of the constructor sequence *)
Definition SequenceT (ty : type) := maketype (sequence ty).


(** * Some predicates on types *)

Inductive isValue : type ->  Prop :=
| wordIsValue        {n : nat} : isValue (word n)
| vectorIsValue      {n : nat}{t : type} :  isValue (vector n t)
.

Inductive isBounded : type -> Prop :=
| wordIsBounded      {n : nat} : isBounded (word n)
| vectorIsBounded    {n : nat}{t : type} : isBounded (vector n t)
| arrayIsBounded     {n : nat}{e : endian}{t : type} : isBounded (array n e t)
.
