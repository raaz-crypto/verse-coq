Require Import NArith.
Require Import Verse.BitVector.
Require Import Verse.BitVector.Facts.
Require Import Psatz.

Require Import Verse.Bounded.
Create HintDb localdb.
(* Bounded bitvector *)
Definition BBvector sz := Bounded (Bvector sz) (@Bv2N sz).

Hint Unfold addition multiplication : localdb.
Hint Rewrite Bv2N_plus_mod Bv2N_mul_mod : localdb.
Ltac local_crush :=
  autounfold with localdb;
  autorewrite with localdb;
  intros;
  let Hmod := fresh "Hmod" in
  let HltRhs := fresh "HltRhs" in
  match goal with
  | [ |- (?E mod ?M < ?RHS)%N ] => assert (Hmod: (E mod M <= E)%N) by (rewrite N.mod_le; eauto with Nfacts);
                                 assert (HltRhs: (E < RHS)%N) by eauto with Nfacts;
                                 apply (N.le_lt_trans _ _ _ Hmod HltRhs)

  end.

Lemma plus_bound {sz} (v1 v2 : Bvector sz)(n1 n2 : N) : (Bv2N v1 < n1 -> Bv2N v2 < n2 -> Bv2N (addition v1 v2) < n1+n2)%N.
  local_crush.
Qed.

Lemma mul_bound {sz} (v1 v2 : Bvector sz)(n1 n2 : N) : (Bv2N v1 < n1 -> Bv2N v2 < n2 -> Bv2N (multiplication v1 v2) < n1*n2)%N.
  local_crush.
Qed.

#[export] Program Instance zero_bbvector sz : Zero (BBvector sz) := bounded zero 1 _.
Next Obligation.
  rewrite Bv2N_zero; lia.
Qed.

#[export] Program Instance one_bbvector sz : One (BBvector (S sz)) := bounded one 2 _.
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



  (** We have the following function diagrams which commutes. *)

(**

 <<
     BBvector  ----- toBN ---> BN
       |                        |
       | forget               forget
       |                        |
       v                        v
     Bvector ------- Bv2N-----> N

>>

*)

Lemma forget_Bv2N_comm {sz} : forall bv : BBvector sz, Bv2N (forget bv) = forget (toBN bv).
  intros.
  simpl.
  trivial.
Qed.
