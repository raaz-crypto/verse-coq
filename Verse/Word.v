(* begin hide *)
Require Import Bvector.
Require Import Coq.ZArith.Zdigits.


(** * Words.

We give an implementation of n-bit words that is useful in to capture
the meanings of

*)



Inductive t (n : nat) : Type :=
| bits : Bvector n -> t n.

Arguments bits [n] _.
  

(** This function lifts a numeric binary function  to WORDS *)
Definition numBinOp {n} f  (x y : t n) : t n :=
  match x, y with
  | bits xv, bits yv => bits (Z_to_binary n (f (binary_value n xv)(binary_value n yv)))
  end.

(** This function lifts a numeric unary function to WORDS *)
Definition numUnaryOp {n : nat} f (x : t n) : t n :=
  match x with
  | bits xv => bits (Z_to_binary n (f (binary_value n xv)))
  end.

(** We also give a way to define bitwise operations on the t type *)

Definition bitwiseBinOp {n : nat} f (x y : t n) : t n :=
  match x,y with
  | bits xv, bits yv => bits (Vector.map2 f xv yv)
  end.

Definition bitwiseUnaryOp {n : nat} f (x : t n) : t n :=
  match x with
  | bits xv => bits (Vector.map f xv )
  end.

