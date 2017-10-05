Require Import Verse.Error.
Require Import Verse.Word.
Require Import Nat.
Require Streams.
Require Import BinInt.

(** * Types in Verse.

Given below is the inductive type that captures data types used in the
verse EDSL.

*)

Inductive type       : Type :=
| word               : nat -> type
| vector             : nat -> type -> type
| array              : nat -> endian -> type -> type
with endian : Type := bigE | littleE | hostE.

(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)

(** ** Sematics of [type].

The semantics of verse types is given by mapping it into types in
coq. While the means of array and sequence are obvious, words are
usually of sizes [power2n] bytes for some [n]. Hence, [word n] denotes
words of [power2n] bytes and hence [typeDenote (word n)] is [Word.t
(power2n * power2p3) = Word.t power2np3]. Similary [vector n _]
denotes a vector of [power2n] elements.

*)

Fixpoint typeDenote (t : type) : Type :=
  match t with
    | word   n       => Word.t (2^(n+3))
    | vector n tw    => Vector.t (typeDenote tw) (2^n)
    | array  n _ tw  => Vector.t (typeDenote tw) n
  end.

(** *** Bitwise and numeric functions.

Now that we know what the [ty : type] means as a type in Coq, we would
like to give meanings to some numeric and bitwise operators
operations.

*)

Fixpoint numBinaryDenote (f : Z -> Z -> Z) t : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word n        => numBinOp f
  | vector n tw   => Vector.map2 (numBinaryDenote f tw)
  | array  n _ tw => Vector.map2 (numBinaryDenote f tw)
  end.

Fixpoint numUnaryDenote (f : Z -> Z)(t : type) : typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 with
  | word n        => numUnaryOp f
  | vector n tw   => Vector.map (numUnaryDenote f tw)
  | array  n _ tw => Vector.map (numUnaryDenote f tw)
  end.

Fixpoint bitwiseBinaryDenote (f : bool -> bool -> bool) t : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word n        => bitwiseBinOp f
  | vector n tw   => Vector.map2 (bitwiseBinaryDenote f tw)
  | array  n _ tw => Vector.map2 (bitwiseBinaryDenote f tw)
  end.

Fixpoint bitwiseUnaryDenote (f : bool -> bool)(t : type) : typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 with
  | word n        => bitwiseUnaryOp f
  | vector n tw   => Vector.map (bitwiseUnaryDenote f tw)
  | array  n _ tw => Vector.map (bitwiseUnaryDenote f tw)
  end.



(** ** Well formed types

There are some restrictions on the type that can be used in actual
programs. For example, one can define vectors only of word types,
arrays cannot be defined on anything but vectors or word. We provide
the combinators [WordT], [VectorT], [ArrayT], and [SequenceT], which
are the smart variants of the constructors [word], [vector], [array],
and [sequence] respectively, which also ensures that the type thus
constructed are all well formed.

*)

Inductive BadType : Prop := BadVector | BadArray.


(** Checks the well formedness of the type *)
Fixpoint typeCheck (ty : type) : type + {BadType}
  :=
  match ty with
  | word _                   => inleft ty
  | vector m (word n)        => inleft ty
  | vector _ _               => inright BadVector
  | array  _ _ (array _ _ _) => inright BadArray
  | array  m e typ           => array m e <$> typeCheck typ
  end.

(** Makes type smartly, i.e. typeCheck and recover the type *)
Definition maketype (ty : type)                        := recover (typeCheck ty).



(** Same as word for consistency with other smart constructors *)
Definition WordT    n                                  := word n.

(** Smart variant of the constructor [vector] *)
Definition VectorT  (n : nat) (ty : type)              := maketype (vector n ty).

(** Smart variant of the constructor [array] *)
Definition ArrayT   (n : nat) (e : endian) (ty : type) := maketype (array n e ty).


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
