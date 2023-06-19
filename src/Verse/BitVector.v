(**

This exposes all the operators on bitvector which is used to give
semantics.

 *)
Require Export Bvector.
Require Import BinNat.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Nat.
Require Import SetoidClass.


Declare Scope bitvector_scope.
Delimit Scope bitvector_scope with bitvector.

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

(** Generate a bit vector with 1 in all bits between m and n
    (inclusive) and zero otherwise. Used to select a particular range
    of values.

*)

Definition onesAt sz (pos : nat) (len : nat): Bvector sz
  := BVxor sz (lower_ones sz (len+pos)) (lower_ones sz pos).

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
Arguments onesAt     [sz].
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

Definition bveq {sz}(v1 v2 : Bvector sz) := BVeq sz sz v1 v2.




(** * Notations for bitvector operations

We define instances for Algebraic syntax for bitvector. This gives
pretty arithmetic operations for bitvectors.

The bitwise operations are given unicode syntax and are used primarily
so that the proof obligations turn out to readable. They are not meant
for input.

TODO: Note that we have hidden the notation that uses unicode so that
coqdoc's pdf generation does not get stuck.

*)

(* begin hide *)
Require Export setoid_ring.Algebra_syntax.

(* Note : The following typeclasses (somehow) allow operators to be
used when writing bitvector annotations. Typeclass unification
allowing delayed unification is the favored theory as to why.
 *)
Class AND A := And : A -> A -> A.
Class OR  A := Or  : A -> A -> A.
Class XOR A := Xor : A -> A -> A.
Class NOT A := Not : A -> A.

#[export] Instance BV_and sz : AND (Bvector sz) := @BVand sz.
#[export] Instance BV_or  sz : OR (Bvector sz)  := @BVor sz.
#[export] Instance BV_xor sz : XOR (Bvector sz) := @BVxor sz.
#[export] Instance BV_not sz : NOT (Bvector sz) := @BVcomp sz.

#[export] Instance zero_Bvector sz : Zero (Bvector sz)     := N2Bv_sized sz 0.
#[export] Instance one_Bvector sz  : One (Bvector sz)      := N2Bv_sized sz 1.
#[export] Instance add_Bvector sz  : Addition (Bvector sz) := @BVplus sz.
#[export] Instance mul_Bvector sz  : Multiplication  := @BVmul sz.
#[export] Instance sub_Bvector sz  : Subtraction (Bvector sz) := @BVminus sz.
#[export] Instance opp_Bvector sz  : Opposite (Bvector sz)   := (@BVnegative sz).

#[export] Instance setoid_bvector sz : Setoid (Bvector sz) := {| SetoidClass.equiv := eq |}.

(* end hide *)
Definition of_Z {sz} (z :  Z) : Bvector sz:=
  match z with
  | Z0 => zero
  | Zpos zp => of_N (Npos zp)
  | Zneg zp => BVnegative (of_N (Npos zp))
  end.

Definition to_Z {sz}(bv : Bvector sz) := Z.of_N (to_N bv).

Fixpoint pow {sz}(eta : Bvector sz)(n : nat) : Bvector sz :=
  match n with
  | 0   => 1
  | S m => (eta  * (pow eta m))
  end.

#[export] Instance bitvector_power_nat (sz : nat) : Power := @pow sz.

Infix "=?" := (bveq) (at level 70): bitvector_scope.
(* begin hide *)

Infix "/"           := BVquot      (at level 40, left associativity) : bitvector_scope.
Infix "%"           := BVrem       (at level 40, left associativity) : bitvector_scope.

Infix "&" := And (at level 56).
Infix "⊕" := Xor (at level 57).
Infix "∣"  := Or (at level 59, left associativity).

Infix "&" := BVand (at level 56, only printing) : bitvector_scope.
Infix "⊕" := BVxor (at level 57, only printing) : bitvector_scope.
Infix "∣"  := BVor (at level 59, left associativity, only printing) : bitvector_scope.


(* TODO : `~` should be < level 40. But conformance with some other
          `~` makes it 75 here *)
Notation "~ E" := (not E)  (at level 75, right associativity).

(* TODO : Why do we have bitvector_scope at all? These notations don't
          really overload any existing notations.
*)
Notation "A ≫ m" := (BVshiftR m A) (at level 54, left associativity) : bitvector_scope.
Notation "A ≪ m" := (BVshiftL m A) (at level 54, left associativity) : bitvector_scope.
Notation "A ⋘ m" := (BVrotL m A)   (at level 54, left associativity) : bitvector_scope.
Notation "A ⋙ m" := (BVrotR m A)   (at level 54, left associativity) : bitvector_scope.
Notation "⟦ A ⟧"  := (@Bv2N _ A) : bitvector_scope.
(* end hide *)
