Require Import NArith.
Require Import Verse.BitVector.
Require Import Verse.BitVector.Facts.
Require Import Psatz.

Require Import Verse.Bounded.
(* Bounded bitvector *)
Definition BBvector sz := Bounded (Bvector sz) (@Bv2N sz).

Lemma plus_bound {sz} (v1 v2 : Bvector sz)(n1 n2 : N) : (Bv2N v1 <= n1 -> Bv2N v2 <= n2 -> Bv2N (addition v1 v2) <= n1+n2)%N.
  intros.
  unfold addition.
  rewrite Bv2N_plus_mod.
  rewrite N.mod_le; eauto with Nfacts.
  Show Proof.
Qed.

Lemma mul_bound {sz} (v1 v2 : Bvector sz)(n1 n2 : N) : (Bv2N v1 <= n1 -> Bv2N v2 <= n2 -> Bv2N (multiplication v1 v2) <= n1*n2)%N.
  intros.
  unfold multiplication.
  rewrite Bv2N_mul_mod.
  rewrite N.mod_le; eauto with Nfacts.
Qed.

#[export] Program Instance zero_bbvector sz : Zero (BBvector sz) := bounded zero 0 _.
Next Obligation.
  rewrite Bv2N_zero; lia.
Qed.

#[export] Program Instance one_bbvector sz : One (BBvector (S sz)) := bounded one 1 _.
Next Obligation.
  rewrite Bv2N_false; lia.
Qed.

#[export] Instance add_bbvector sz : Addition (BBvector sz) :=
  fun bv1 bv2 => match bv1, bv2 with
              | bounded v1 n1 pf1 , bounded v2 n2 pf2 => bounded (v1 + v2) (n1 + n2)%N (plus_bound v1 v2 n1 n2 pf1 pf2)
              end.


#[export] Instance mul_bbvector sz : @Multiplication (BBvector sz) (BBvector sz) :=
  fun bv1 bv2 => match bv1, bv2 with
              | bounded v1 n1 pf1 , bounded v2 n2 pf2 => bounded (v1 * v2) (n1 * n2)%N (mul_bound v1 v2 n1 n2 pf1 pf2)
              end.
