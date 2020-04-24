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
