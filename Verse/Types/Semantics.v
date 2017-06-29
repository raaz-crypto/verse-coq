Require Import Verse.Types.Internal.

(* begin hide *)
Require Vector.
Require Streams.
Require Import Bvector.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.Zdigits.
Require Import BinInt.
Require Import Nat.
Open Scope nat_scope.

(* end hide *)

(** * Sematics of types.

Firstly, we define the type WORD to capture bit vectors.

*)



Inductive WORD (n : nat) : Type :=
| WORD_BITS : Bvector n -> WORD n.

Arguments WORD_BITS [n] _.


(**

The semantics of verse types is given by mapping it into types in
coq. Notice that [word n] denotes words that are [2^n] bytes long.
and hence [typeDenote (word n) is [WORD(2^(n) * 2 ^ 3)].

*)
Fixpoint typeDenote (t : type) : Type :=
  match t with
    | word   n      => WORD (2^(n+3))
    | vector n tw   => Vector.t (typeDenote tw) (2^n)
    | array  n _ tw => Vector.t (typeDenote tw) n
    | sequence tw   => Streams.Stream (typeDenote tw)
  end.

(** ** Truncated numeric functions on WORD

The [WORD n] type can be seen as integers modulo 2^n. Numerical
functions can then be defined on the word type applying the function
and truncating module [2^n]. The combinators [numBinOp] and
[numUnaryOp] are helper functions to define such variants.

*)

(** This function lifts a numeric binary function  to WORDS *)
Definition numBinOp {n} f  (x y : WORD n) : WORD n :=
  match x, y with
  | WORD_BITS xv, WORD_BITS yv => WORD_BITS (Z_to_binary n (f (binary_value n xv)(binary_value n yv)))
  end.

(** This function lifts a numeric unary function to WORDS *)
Definition numUnaryOp {n : nat} f (x : WORD n) : WORD n :=
  match x with
  | WORD_BITS xv => WORD_BITS (Z_to_binary n (f (binary_value n xv)))
  end.

(** We also give a way to define bitwise operations on the WORD type *)

Definition bitwiseBinOp {n : nat} f (x y : WORD n) : WORD n :=
  match x,y with
  | WORD_BITS xv, WORD_BITS yv => WORD_BITS (Vector.map2 f xv yv)
  end.

Definition bitwiseUnaryOp {n : nat} f (x : WORD n) : WORD n :=
  match x with
  | WORD_BITS xv => WORD_BITS (Vector.map f xv )
  end.


(** We now give the meanings of numeric and bitwise functions when the act on the types in Verse *)

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

Fixpoint bitwiseBinaryDenote (f : bool -> bool -> bool) t : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word n        => bitwiseBinOp f
  | vector n tw   => Vector.map2 (bitwiseBinaryDenote f tw)
  | array  n _ tw => Vector.map2 (bitwiseBinaryDenote f tw)
  | sequence tw   => Streams.zipWith (bitwiseBinaryDenote f tw)
  end.

Fixpoint bitwiseUnaryDenote (f : bool -> bool)(t : type) : typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 with
  | word n        => bitwiseUnaryOp f
  | vector n tw   => Vector.map (bitwiseUnaryDenote f tw)
  | array  n _ tw => Vector.map (bitwiseUnaryDenote f tw)
  | sequence tw   => Streams.map (bitwiseUnaryDenote f tw)
  end.


Definition plus  := numBinaryDenote Z.add.
Definition minus := numBinaryDenote Z.sub.
