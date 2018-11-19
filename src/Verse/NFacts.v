Require Import BinNums.
Require Import BinInt.

Require Import NArith.
Require Import Verse.CoLoR_VecUtil.

Definition two_power_nat_N n := (2 ^ N.of_nat n)%N.

Lemma two_power_nonzero n : two_power_nat_N n <> 0%N.
  now apply N.pow_nonzero.
Qed.

Lemma N2Bv_gen_Sn n N : N2Bv_gen (S n) N = Bvector.Bcons (N.odd N) n (N2Bv_gen n (N.div2 N)).
  induction N.
  * simpl.
    induction n.
    - trivial.
    - simpl.
      unfold Bvector.Bcons.
      f_equal.
  * induction p.
    - simpl. f_equal.
    - simpl. f_equal.
    - simpl. f_equal.
      induction n.
      + trivial.
      + simpl. f_equal.
Qed.

Lemma N2Bv_gen_O n : N2Bv_gen n 0 = Bvector.Bvect_false n.
  induction n.
  trivial.
  simpl.
  trivial.
Qed.

Lemma Bv2N_Sn n b bv : Bv2N (S n) (b :: bv) = ((N.b2n b) + 2 * Bv2N n bv)%N.
  simpl.
  destruct b.
  destruct (Bv2N n bv); trivial.
  destruct (Bv2N n bv); trivial.
Qed.

Lemma N_size_eq_N_size_nat : forall N, N.size N = N.of_nat (N.size_nat N).
  induction N.
  trivial.

  unfold N.size.
  unfold N.size_nat.
  unfold N.of_nat.
  induction p.
  simpl; f_equal.
  destruct p; simpl in *; congruence.

  simpl; f_equal.
  destruct p; simpl in *; congruence.

  simpl; f_equal.
Qed.

Lemma Bv2N_small n b : (Bv2N n b < two_power_nat_N n)%N.
Proof.
  assert (N.of_nat (N.size_nat (Bv2N n b)) <= N.of_nat n)%N.
  unfold N.le.
  rewrite <- Nat2N.inj_compare.
  apply Compare_dec.nat_compare_le.
  apply Bv2N_Nsize.

  rewrite <- N_size_eq_N_size_nat in H.
  pose (N.size_gt (Bv2N n b)).
  eapply (N.lt_le_trans _ _ _ l _).
  Unshelve.
  apply N.pow_le_mono_r.
  discriminate.
  trivial.
Qed.

Lemma Bv2N_N2Bv_gen_mod n : forall N, Bv2N _ (N2Bv_gen n N) = N.modulo N (two_power_nat_N n).
  induction n.
  unfold two_power_nat_N.
  auto using N.mod_1_r.

  intros.
  unfold two_power_nat_N.
  rewrite N2Bv_gen_Sn.
  rewrite Bv2N_Sn.
  rewrite IHn.
  rewrite Nat2N.inj_succ.
  rewrite N.pow_succ_r.
  rewrite N.mod_mul_r.
  rewrite N.div2_div.
  rewrite N.add_cancel_r.
  rewrite <- N.bit0_mod.
  f_equal.
  auto using N.bit0_odd.
  discriminate.
  apply N.pow_nonzero.
  discriminate.
  destruct n.
  discriminate.
  discriminate.
Qed.

Lemma Bv2N_inj n b1 b2 : Bv2N n b1 = Bv2N n b2 <-> b1 = b2.
  constructor; intros.
  pose (f_equal (N2Bv_gen n) H).
  now rewrite ?N2Bv_Bv2N in e.
  now apply f_equal.
Qed.

Lemma N2Bv_trunc n N : N2Bv_gen n N = N2Bv_gen n (N mod two_power_nat_N n).
  apply Bv2N_inj.
  rewrite ?Bv2N_N2Bv_gen_mod.
  rewrite N.mod_mod.
  trivial.
  now apply N.pow_nonzero.
Qed.
