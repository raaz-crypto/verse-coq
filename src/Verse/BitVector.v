(**

This exposes all the operators on bitvector which is used to give
semantics.

 *)
Require Export Bvector.
Require Import BinNat.
Require Import Arith.
Require Import NArith.
Require Import Nat.

(** computes 2^m *)
Definition twopower m : N
  := iter m N.double 1%N.

Definition arithm (func : N -> N -> N) sz : Bvector sz -> Bvector sz -> Bvector sz
  := fun x y => N2Bv_sized sz (func (@Bv2N _ x) (@Bv2N _ y)).

Definition BVplus      := arithm N.add.
Definition BVminus sz  := arithm (fun x y => x + (twopower sz - y))%N sz.
Definition BVmul       := arithm N.mul.
Definition BVquot      := arithm N.div.
Definition BVrem       := arithm N.modulo.


Check BVand. (* Comes directly from Bvector *)
Check BVor.  (* Comes directly from Bvector *)
Check BVxor. (* Comes directly from Bvector *)

Definition BVComp   := Bneg. (* renaming for better naming convention *)

Definition BVshiftL sz (n : nat) : Bvector sz -> Bvector sz :=
  match sz with
  | 0%nat   => fun vec => vec
  | S sz0 => fun vec => BshiftL_iter sz0 vec n
  end.

Definition BVshiftR sz (n : nat) : Bvector sz -> Bvector sz :=
  match sz with
  | 0%nat   => fun vec => vec
  | S sz0 => fun vec => BshiftRl_iter sz0 vec n
  end.

Definition rotOnce sz (vec : Bvector sz) :=
  match vec with
  | [] => []
  | (x :: xs) => Vector.shiftin x xs
  end.

Definition BVrotR sz n
  := let r := n mod sz in iter n (rotOnce sz).

Definition BVrotL sz n
  := let r := n mod sz in iter (sz - n) (rotOnce sz).

(** Generates a bit vector with n-lsb bits set *)
Definition lower_ones sz n : Bvector sz
  := N2Bv_sized sz (N.ones (N.of_nat n)).

(** Generate a bit vector with n-msb bits set *)
Definition upper_ones sz n : Bvector sz
  := BVComp sz (lower_ones sz (sz - n)).

(* begin hide *)
Arguments BVplus   [sz].
Arguments BVminus  [sz].
Arguments BVminus  [sz].
Arguments BVmul    [sz].
Arguments BVquot   [sz].
Arguments BVrem    [sz].
Arguments BVand    [_].
Arguments BVor     [_].
Arguments BVxor    [_].
Arguments BVComp   [_].
Arguments BVshiftL [sz].
Arguments BVshiftR [sz].
Arguments BVrotR   [sz].
Arguments BVrotL   [sz].

Arguments lower_ones [sz].
Arguments upper_ones [sz].
(* end hide *)

(** * Bitwise functions

This function essentially give the semantics of some of the bitwise
macros that we have in the library. Facts about them will help dealing
with semantics.

*)
Definition selectLower {sz} n (vec : Bvector sz) := BVand vec (lower_ones n).
Definition selectUpper {sz} n (vec : Bvector sz) := BVand vec (upper_ones n).
Definition clearUpper {sz}  n  := @selectLower sz (sz -n).
Definition clearLower {sz}  n  := @selectUpper sz (sz - n).

(** Some efficient arithmetic functions using bitwise operations. **)


Definition div2power_nat    {sz} n := @BVshiftR sz n.
Definition modulo2power_nat {sz} n := @selectLower sz n.
Definition Bv2Nat {sz} (vec : Bvector sz) := N.to_nat (@Bv2N _ vec).
