(* begin hide *)
Require Import Bvector.
Require Import Verse.Error.
Require Import Vector.
Require Import Coq.NArith.Ndigits.
Require Import BinNums.
Require Import NArith.
Require Import String.
Require Import Ascii.
Require Import Verse.PrettyPrint.
Require Import Arith.
Require Verse.Nibble.
Import Basics.

Local Open Scope N_scope.

(* end hide *)

(** * Words.

We give an implementation of n-bit words that is useful in to capture
the meanings of

*)



Inductive t (n : nat) : Type :=
| bits : Bvector n -> t n.

Arguments bits [n] _.

Definition bytes n := t (8 * n).

About N2Bv_gen.
Require Verse.Nibble.
Definition fromNibbles {n} (v : Vector.t Verse.Nibble.Nibble n) : t (4 * n) :=
  bits (N2Bv_gen (4 * n) (Verse.Nibble.toN v)).



(**

Conversely we can convert a word constant to its hexadecimal string as
follows:

*)

Definition mapP {T U} (f : T -> U) (p : T * T) :=
  let '(p1, p2) := p in (f p1, f p2).

(* This function lifts numeric operations with overflow *)
Definition numOverflowBinop {n} f (x y : t n) : t n * t n :=
  let break_num m := (m / 2 ^ (N.of_nat n), m)
  in
  match x, y with
  | bits xv, bits yv =>  mapP (compose (@bits n) (N2Bv_gen n))
                                 (break_num (f (Bv2N n xv) (Bv2N n yv)))
  end.

(* This function lifts a numeric binop with one big argument and two outputs *)
Definition numBigargExop {n} f (x y z : t n) : t n * t n :=
  let make_big x y := (2 ^ (N.of_nat n) * x + y) in
  match x, y, z with
  | bits xv, bits yv, bits zv => mapP (compose (@bits n) (N2Bv_gen n))
                                         (f (make_big (Bv2N n xv) (Bv2N n yv))
                                            (Bv2N n zv))
  end.

(** This function lifts a numeric binary function to the word type *)
Definition numBinOp {n} f  (x y : t n) : t n :=
  match x, y with
  | bits xv, bits yv => bits (N2Bv_gen n (f (Bv2N n xv)(Bv2N n yv)))
  end.

(** This function lifts a numeric unary function to the word type *)
Definition numUnaryOp {n : nat} f (x : t n) : t n :=
  match x with
  | bits xv => bits (N2Bv_gen n (f (Bv2N n xv)))
  end.

Definition liftBV (f : forall n,  Bvector n -> Bvector n) : forall n, t n -> t n :=
  fun n x  =>
    match x with
    | bits xv => bits (f n xv)
    end.

Definition liftBV2 (f : forall n,  Bvector n  -> Bvector n -> Bvector n) : forall n , t n -> t n -> t n :=
  fun n x y =>
    match x,y with
    | bits xv, bits yv => bits (f n xv yv)
    end.

Definition AndW n := liftBV2 BVand n.
Definition OrW  n := liftBV2 BVor  n.
Definition XorW n := liftBV2 BVxor n.
Definition NegW n := liftBV  Bneg  n.

Module BOps.
  Definition BShiftL m (n : nat) :=
    match n with
    | 0%nat    => fun vec => vec
    | S np => fun vec => BshiftL_iter np vec m
    end.

  Definition BShiftR m (n : nat) :=
    match n with
    | 0%nat  => fun vec => vec
    | S np   => fun vec => BshiftRl_iter np vec m
    end.

  Definition BRotL m n : Bvector n -> Bvector n :=
    fun vec => BVor n (BShiftL m n vec) (BShiftR (n - m) n vec).

  Definition BRotR m n : Bvector n -> Bvector n :=
    fun vec => BVor n (BShiftR m n vec) (BShiftL (n - m) n vec).

End BOps.

Definition ShiftL m := liftBV (BOps.BShiftL m).
Definition ShiftR m := liftBV (BOps.BShiftR m).
Definition RotL m := liftBV (BOps.BRotL m).
Definition RotR m := liftBV (BOps.BRotR m).
