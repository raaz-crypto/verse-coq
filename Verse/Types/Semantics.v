Require Import Verse.Types.Internal.
Require Vector.
Require Streams.
Require Import Bvector.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zdigits.
Require Import BinInt.
Require Import Nat.
(**

We now give a semantics of type. The function typeDenote gives a definition from

 *)

Open Scope nat_scope.

(* n-bit word *)
Inductive WORD (n : nat) : Type :=
| WORD_BITS : Bvector n -> WORD n.

Arguments WORD_BITS [n] _.

Definition numBinOp {n} f  (x y : WORD n) : WORD n :=
  match x, y with
  | WORD_BITS xv, WORD_BITS yv => WORD_BITS (Z_to_binary n (f (binary_value n xv)(binary_value n yv)))
  end.

Definition numUnaryOp {n : nat} f (x : WORD n) : WORD n :=
  match x with
  | WORD_BITS xv => WORD_BITS (Z_to_binary n (f (binary_value n xv)))
  end.

Definition bitwiseBinOp {n : nat} f (x y : WORD n) : WORD n :=
  match x,y with
  | WORD_BITS xv, WORD_BITS yv => WORD_BITS (Vector.map2 f xv yv)
  end.

Definition bitwiseUnaryOp {n : nat} f (x : WORD n) : WORD n :=
  match x with
  | WORD_BITS xv => WORD_BITS (Vector.map f xv )
  end.


Fixpoint typeDenote (t : type) : Type :=
  match t with
    | word   n      => WORD (2^(n+3))                   (** 2^n bytes = 2^n * 2^3 bits *)
    | vector n tw   => Vector.t (typeDenote tw) (2^n)
    | array  n _ tw => Vector.t (typeDenote tw) n
    | sequence tw   => Streams.Stream (typeDenote tw)
  end.


(** Meaning of the binary operator at at the given type_ *)


Fixpoint numBinaryDenote (f : Z -> Z -> Z) t : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word n        => numBinOp f
  | vector n tw   => Vector.map2 (numBinaryDenote f tw)
  | array  n _ tw => Vector.map2 (numBinaryDenote f tw)
  | sequence tw   => Streams.zipWith (numBinaryDenote f tw)
  end.

Fixpoint numUnaryDenote (f : Z -> Z)(t : type) : typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 with
  | word n        => numUnaryOp f
  | vector n tw   => Vector.map (numUnaryDenote f tw)
  | array  n _ tw => Vector.map (numUnaryDenote f tw)
  | sequence tw   => Streams.map (numUnaryDenote f tw)
  end.

Definition plus  := numBinaryDenote Z.add.
Definition minus := numBinaryDenote Z.sub.
