(* begin hide *)
Require Import Bvector.
Require Import Vector.
Require Import Coq.ZArith.Zdigits.
Require Import String.

(** * Words.

We give an implementation of n-bit words that is useful in to capture
the meanings of

*)



Inductive t (n : nat) : Type :=
| bits : Bvector n -> t n.

Arguments bits [n] _.

Arguments nil [A].


Definition toZ {n}(x : t n) :=
  match x with
  | bits bv => binary_value n bv
  end.

Open Scope string_scope.

Definition bitsToHex {n} (x : t n) : string :=
  let 'bits bv := x in
  let bv' := rev_append_tail bv nil in
  (fix vth {n} (v : Bvector n) : string :=
  match v with
  | false :: false :: false :: false :: vt => vth vt ++ "0"
  | true :: false :: false :: false :: vt  => vth vt ++ "1"
  | false :: true :: false :: false :: vt  => vth vt ++ "2"
  | true :: true :: false :: false :: vt   => vth vt ++ "3"
  | false :: false :: true :: false :: vt  => vth vt ++ "4"
  | true :: false :: true :: false :: vt   => vth vt ++ "5"
  | false :: true :: true :: false :: vt   => vth vt ++ "6"
  | true :: true :: true :: false :: vt    => vth vt ++ "7"
  | false :: false :: false :: true :: vt  => vth vt ++ "8"
  | true :: false :: false :: true :: vt   => vth vt ++ "9"
  | false :: true :: false :: true :: vt   => vth vt ++ "a"
  | true :: true :: false :: true :: vt    => vth vt ++ "b"
  | false :: false :: true :: true :: vt   => vth vt ++ "c"
  | true :: false :: true :: true :: vt    => vth vt ++ "d"
  | false :: true :: true :: true :: vt    => vth vt ++ "e"
  | true :: true :: true :: true :: vt     => vth vt ++ "f"
  | false :: false :: false :: nil         => "x0"
  | true :: false :: false :: nil          => "x1"
  | false :: true :: false :: nil          => "x2"
  | true :: true :: false :: nil           => "x3"
  | false :: false :: true :: nil          => "x4"
  | true :: false :: true :: nil           => "x5"
  | false :: true :: true :: nil           => "x6"
  | true :: true :: true :: nil            => "x7"
  | false :: false :: nil                  => "x0"
  | true :: false :: nil                   => "x1"
  | false :: true :: nil                   => "x2"
  | true :: true :: nil                    => "x3"
  | false :: nil                           => "x0"
  | true :: nil                            => "x1"
  | nil                                    => "x"
  end) _ bv'.

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

