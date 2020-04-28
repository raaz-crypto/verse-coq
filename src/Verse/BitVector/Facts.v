Require Import BinNat.
Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.
Require Import Omega.


Hint Rewrite Nat.add_1_r        : bitvector.
Hint Rewrite Nat.add_0_r        : bitvector.
Hint Rewrite Nat.double_twice   : bitvector.

Hint Rewrite Nat.double_twice : NatN.
Hint Rewrite Nat2N.inj_double Nat2N.inj_succ_double
     Nat2N.inj_succ Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub
     Nat2N.inj_pred Nat2N.inj_div2 Nat2N.inj_max Nat2N.inj_min
     Nat2N.id
  : NatN.

Ltac crush := repeat (simpl; trivial;
                      match goal with
                      | [ |- ?b : bool ] => destruct b
                      | [ |- N.to_nat _ = _ ] => autorewrite with Nnat
                      | [ |- N.of_nat _ = _ ] => autorewrite with NatN
                      | _ => autorewrite with bitvector;  eauto; idtac
                      end).

Ltac induct_crush n :=
  induction n as [|n IHn]; crush; rewrite IHn; crush.

Lemma twopower_nat_spec : forall n, twopower_nat n = 2^n.
  intro n; induction n; crush.
Qed.

Lemma twopower_to_nat : forall n, N.to_nat (twopower n) = twopower_nat n.
  intro n;unfold twopower; unfold twopower_nat.
  induction n; crush.
Qed.

Lemma twopower_spec : forall n : nat, N.to_nat (twopower n) = 2^n.
  intro n; rewrite twopower_to_nat; rewrite twopower_nat_spec; trivial.
Qed.

Lemma twopower_of_nat : forall n, N.of_nat (twopower_nat n) = twopower n.
  intro n.
  induct_crush n.
Qed.

Lemma N2Nat_inj_if : forall (b : bool) (x y : N),
    N.to_nat (if b then x else y) = (if b then N.to_nat x else N.to_nat y).
  intros b x y; destruct b; trivial.
Qed.
