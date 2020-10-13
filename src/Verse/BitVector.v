(**

This exposes all the operators on bitvector which is used to give
semantics.

 *)
Require Export Bvector.
Require Import BinNat.
Require Import Arith.
Require Import NArith.
Require Import Nat.

Declare Scope bitvector_scope.

Arguments Bv2N [n].

(** computes 2^m *)
Definition twopower m : N := Nat.iter m N.double 1%N.
Definition twopower_nat (m:nat) : nat := Nat.iter m Nat.double 1.
Definition twopower_N   (m:N) : N := N.iter m N.double 1%N.
Definition arithm (func : N -> N -> N) sz : Bvector sz -> Bvector sz -> Bvector sz
  := fun x y => N2Bv_sized sz (func (@Bv2N _ x) (@Bv2N _ y)).

Definition BVN_size {sz} (vec : Bvector sz) := N.size (Bv2N vec).
Definition BVN_size_nat {sz} (vec : Bvector sz) := N.size_nat (Bv2N vec).

Definition BVplus      := arithm N.add.
Definition BVnegative sz (vec : Bvector sz) := N2Bv_sized sz (2^(N.of_nat sz) - Bv2N vec).
Definition BVminus sz  := arithm (fun x y => x + 2^(N.of_nat sz) - y)%N sz.

Definition BVmul       := arithm N.mul.
Definition BVquot      := arithm N.div.
Definition BVrem       := arithm N.modulo.

Definition BVones : forall sz, Bvector sz
  := Bvect_true.
Definition BVzeros : forall sz, Bvector sz
  := Bvect_false.


Check BVand. (* Comes directly from Bvector *)
Check BVor.  (* Comes directly from Bvector *)
Check BVxor. (* Comes directly from Bvector *)

Definition BVcomp   := Bneg. (* renaming for better naming convention *)

Definition BVshiftL1 sz : Bvector sz -> Bvector sz :=
  match sz with
  | 0 => @id (Bvector 0)
  | S sz0 => fun vec => BshiftL sz0 vec false
  end.

Definition BVshiftL sz (n : nat) : Bvector sz -> Bvector sz
  := Nat.iter n (BVshiftL1 sz).

Definition BVshiftR1 sz : Bvector sz -> Bvector sz :=
  match sz with
  | 0 => @id (Bvector 0)
  | S sz0 => fun vec => BshiftRl sz0 vec false
  end.

Definition BVshiftR sz (n : nat) : Bvector sz -> Bvector sz
  := Nat.iter n (BVshiftR1 sz).

Definition rotTowardsLSB sz (vec : Bvector sz) :=
  match vec with
  | [] => []
  | (x :: xs) => Vector.shiftin x xs
  end.

(** This is what shiftout should have been not sure why it was not defined this way *)
Definition popout {A} : forall n, Vector.t A (S n) -> (Vector.t A n * A) :=
  @Vector.rectS _ (fun n _ => (Vector.t A n * A)%type)
           (fun a => ([], a))
           (fun h _ _ H => let (xs, x) := H in (h :: xs, x)).

Arguments popout [A n].

Definition rotTowardsMSB sz (vec : Bvector sz) :=
  match vec with
  | [] => []
  | xs => let (xsp, x) := popout xs in (x :: xsp)
  end.

Definition BVrotR sz n
  := Nat.iter n (rotTowardsLSB sz).

Definition BVrotL sz n
  := Nat.iter n (rotTowardsMSB sz).

(** Generates a bit vector with n-lsb bits set *)
Definition lower_ones sz n : Bvector sz
  := N2Bv_sized sz (N.ones (N.of_nat n)).

(** Generate a bit vector with n-msb bits set *)
Definition upper_ones sz n : Bvector sz
  := BVcomp sz (lower_ones sz (sz - n)).

(* begin hide *)
Arguments BVplus   [sz].
Arguments BVminus  [sz].
Arguments BVmul    [sz].
Arguments BVquot   [sz].
Arguments BVrem    [sz].
Arguments BVnegative [sz].
Arguments BVand    [_].
Arguments BVor     [_].
Arguments BVxor    [_].
Arguments BVcomp   [_].
Arguments BVshiftL [sz].
Arguments BVshiftL1 [sz].
Arguments BVshiftR [sz].
Arguments BVshiftR1 [sz].
Arguments BVrotR   [sz].
Arguments BVrotL   [sz].

Arguments lower_ones [sz].
Arguments upper_ones [sz].

Arguments BVzeros {sz}.
Arguments BVones  {sz}.
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
Definition of_N {sz}   : N -> Bvector sz := N2Bv_sized sz.
Definition to_N {sz}   : Bvector sz -> N := @Bv2N sz.
(*
Definition of_nat {sz} : nat -> Bvector sz :=  fun n => N2Bv_sized sz (N.of_nat n).
Definition to_nat {sz} : Bvector sz -> nat := fun vec => N.to_nat (to_N vec).
 *)

(** * Notations for bitvector operations

These pretty printing only notations are used primarily so that the
proof obligations turn out to be beautiful. They are not meant for
input.

TODO: Note that we have hidden the notation that uses unicode so that
coqdoc's pdf generation does not get stuck.

*)


(* begin hide *)


Notation "A & B" := (BVand A B) (only printing, at level 100) : bitvector_scope.
Notation "A | B" := (BVor A B)  (only printing, at level 100) : bitvector_scope.
Notation "~ A"
  := (BVcomp A)
       (only printing, at level 75, right associativity) : bitvector_scope.
Notation "A ⊕ B" := (BVxor A B) (only printing, at level 57, left associativity) : bitvector_scope.
Notation "A ≫ m" := (BVshiftR m A) (only printing, at level 100) : bitvector_scope.
Notation "A ≪ m" := (BVshiftL m A) (only printing, at level 100) : bitvector_scope.
Notation "A ⋘ m" := (BVrotL m A) (only printing, at level 100) : bitvector_scope.
Notation "A ⋙ m" := (BVrotR m A) (only printing, at level 100) : bitvector_scope.
Notation "⟦ A ⟧"  := (@Bv2N _ A)    (only printing) : bitvector_scope.

Infix "+" := (BVplus)  (only printing) : bitvector_scope.
Infix "*" := (BVmul)   (only printing) : bitvector_scope.
Infix "-" := (BVminus) (only printing) : bitvector_scope.
Infix "/" := (BVquot)  (only printing) : bitvector_scope.

(* end hide *)
