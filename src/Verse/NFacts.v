Require Import BinNums.
Require Import ZArith.
Require Import Coq.ZArith.Zdigits.
Require Import ZArith_base.
Require Import BinInt.

Require Import NArith.
Require Import Verse.CoLoR_VecUtil.

Definition two_power_nat_N n := N.pos (shift_nat n 1).

Definition two_power_nat_N_equiv n : two_power_nat_N n = (2 ^ (N.of_nat n))%N.
  unfold two_power_nat_N.
  rewrite Zpower.shift_nat_equiv.
  rewrite Pshiftl_nat_N.
  rewrite <- (Nat2N.id n).
  rewrite Nshiftl_nat_equiv.
  rewrite N.shiftl_1_l.
  now rewrite Nat2N.id.
Qed.

Definition OneGtZero : (0 < 1)%Z.
  apply Pos2Z.is_pos.
Defined.

Lemma two_power_even : forall n, Z.Even (two_power_nat (S n)).
Proof.
  pose (forall n, Z.even (two_power_nat (S n)) = true).
  trivial.
  intros.
  now apply Z.even_spec.
Qed.

Lemma two_power_pos : forall n, (0 < two_power_nat n)%Z.
  intros.
  rewrite two_power_nat_equiv.
  apply Z.pow_pos_nonneg; auto with *.
Qed.

Lemma O_le_binary_value n b : (0 <= binary_value n b)%Z.
  pose (binary_value_pos n b).
  unfold Z.ge in g.
  unfold Z.le.
  contradict g.
  apply Zcompare_Gt_Lt_antisym.
  assumption.
Qed.

Lemma binary_value_small : forall n b, (binary_value n b < two_power_nat n)%Z.
Proof.
  induction n.
  unfold binary_value. simpl.
  - intros; apply two_power_pos.
  - dependent inversion b.
    rewrite binary_value_Sn.
    pose (Zlt_le_succ _ _ (IHn t)).
    rewrite <- Z.add_1_l in l.
    assert (O_le_2 : (0 <= 2)%Z).
      auto with *.
    pose (Z.mul_le_mono_nonneg_l _ _ 2 O_le_2 l).
    rewrite Z.mul_add_distr_l in l0.
    assert (bv_small : (bit_value h < 2)%Z).
      case h; simpl; auto with *.
    rewrite two_power_nat_S.
    pose (Zplus_lt_compat_r _ _ (2 * binary_value n t) bv_small).
    auto with *.
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

Lemma Z_to_binary_O n : Z_to_binary n 0 = Bvector.Bvect_false n.
  induction n.
  trivial.
  simpl.
  unfold Bvector.Bcons.
  f_equal.
  trivial.
Qed.

Lemma N2Bv_gen_Z_to_binary n : forall P, N2Bv_gen n (Npos P) = Z_to_binary n (Zpos P).
  induction n.
  - trivial.
  - intro.
    rewrite N2Bv_gen_Sn.
    rewrite Z_to_binary_Sn_z.
    f_equal.
    * destruct P; trivial.
    * destruct P.
      simpl. apply IHn.
      simpl. apply IHn.
      simpl. induction n.
      trivial.
      rewrite N2Bv_gen_O.
      rewrite Z_to_binary_O.
      trivial.
Qed.

Lemma Bv2N_Sn n b bv : Bv2N (S n) (b :: bv) = (Z.to_N (bit_value b) + 2 * Bv2N n bv)%N.
  simpl.
  destruct b.
  destruct (Bv2N n bv); trivial.
  destruct (Bv2N n bv); trivial.
Qed.

Lemma Bv2N_binary_value n : forall b, Bv2N n b = Z.to_N (binary_value n b).
  intro.
  unfold Bvector.Bvector in b.
  induction n.
  VOtac.
  trivial.
  VSntac b.
  rewrite binary_value_Sn.
  rewrite Bv2N_Sn.
  rewrite IHn.
  assert (Z.to_N 2 = 2%N) by trivial.
  rewrite <- H0.
  erewrite <- Z2N.inj_mul.
  apply eq_sym.
  eapply Z2N.inj_add.
  destruct (Vhead b).
  exact Z.le_0_1.
  apply Z.le_refl.
  apply Z.mul_nonneg_nonneg.
  apply Z.le_0_2.
  apply O_le_binary_value.
  apply Z.le_0_2.
  pose (binary_value_pos n (Vtail b)).
  unfold Z.ge in g.
  unfold Z.le.
  contradict g.
  apply Zcompare_Gt_Lt_antisym.
  assumption.
Qed.


Lemma Bv2N_small n b : (Bv2N n b < two_power_nat_N n)%N.
Proof.
  rewrite Bv2N_binary_value.
  assert (two_power_nat_N n = Z.to_N (two_power_nat n)).
  now unfold two_power_nat_N.
  rewrite H.
  apply Z2N.inj_lt.
  apply O_le_binary_value.
  apply Z.lt_le_incl.
  apply two_power_pos.
  apply binary_value_small.
Qed.

Lemma Z_to_binary_to_Z_mod : forall n z, binary_value n (Z_to_binary n z) = Zmod z (two_power_nat n).
Proof.
  induction n as [| n IHn].
  unfold two_power_nat, shift_nat. simpl. intros.
  assert (bounds : (0 <= z mod 1 < 1)%Z).
  exact (Z.mod_pos_bound z 1 OneGtZero).
  destruct (Z.lt_succ_r (z mod 1) 0) as [X Y].
  destruct bounds as [lower upper].
  apply (Z.le_antisymm _ _ lower (X upper)).

  intros.  rewrite Z_to_binary_Sn_z.
  rewrite binary_value_Sn.
  rewrite IHn.
  pose (Z.div_mod z (two_power_nat (S n))).
  assert (two_power_nat (S n) <> 0%Z).
       unfold two_power_nat.
       discriminate.
  pose (e H).
  rewrite e0 at 1 2.
  rewrite (Z.add_comm _ (z mod (two_power_nat (S n)))).
  rewrite Z.odd_add_mul_even .
  rewrite Z.div2_div.
  rewrite two_power_nat_S at 3.
  rewrite <- (Z.mul_assoc 2). rewrite (Z.mul_comm 2 (two_power_nat n * (z / two_power_nat (S n)))).
  rewrite (Z.div_add).
  rewrite (Z.mul_comm (two_power_nat n)).
  rewrite Z_mod_plus_full.
  rewrite (Zmod_small _ (two_power_nat n)).
  rewrite <- Z.div2_div.
  apply Z_div2_value.
  rewrite Z.ge_le_iff.
  apply Z.mod_pos_bound.
  apply two_power_pos.
  constructor.
  apply Z.div_pos.
  apply Z.mod_pos_bound.
  apply two_power_pos.
  apply Z.lt_0_2.
  rewrite <- Z.div2_div.
  apply Zdiv2_two_power_nat.
  rewrite Z.ge_le_iff.
  apply Z.mod_pos_bound.
  apply two_power_pos.
  apply Z.mod_pos_bound.
  apply two_power_pos.
  discriminate.
  apply two_power_even.
Qed.

Lemma Bv2N_N2Bv_gen_mod n N : Bv2N _ (N2Bv_gen n N) = N.modulo N (two_power_nat_N n).
  destruct N.
  rewrite N.mod_0_l.
  rewrite N2Bv_gen_O.
  induction n.
  trivial.
  simpl.
  rewrite IHn.
  trivial.
  induction n.
  unfold two_power_nat_N.
  discriminate.
  unfold two_power_nat_N.
  discriminate.
  rewrite N2Bv_gen_Z_to_binary.
  rewrite Bv2N_binary_value.
  rewrite Z_to_binary_to_Z_mod.
  apply Z2N.inj_mod.
  apply Zle_0_pos.
  apply two_power_pos.
Qed.

Lemma Bv2N_inj n b1 b2 : Bv2N n b1 = Bv2N n b2 <-> b1 = b2.
  constructor; intros.
  pose (f_equal (N2Bv_gen n) H).
  now rewrite ?N2Bv_Bv2N in e.
  now apply f_equal.
Qed.

Lemma binary_value_inj : forall n b1 b2, binary_value n b1 = binary_value n b2 <-> b1 = b2.
  intros.
  constructor; intros.
  pose (f_equal (Z_to_binary n) H).
  now rewrite ?binary_to_Z_to_binary in e.
  now apply f_equal.
Qed.

Lemma N2Bv_trunc n N : N2Bv_gen n N = N2Bv_gen n (N mod two_power_nat_N n).
  apply Bv2N_inj.
  rewrite ?Bv2N_N2Bv_gen_mod.
  now rewrite N.mod_mod.
Qed.

Lemma Z_to_binary_trunc : forall n z, Z_to_binary n z = Z_to_binary n (z mod two_power_nat n).
  intros.
  apply binary_value_inj.
  rewrite ?Z_to_binary_to_Z_mod.
  now rewrite Z.mod_mod.
Qed.
