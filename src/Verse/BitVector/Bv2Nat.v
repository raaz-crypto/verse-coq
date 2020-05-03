Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.
Require Import Verse.BitVector.Facts.

Hint Unfold  Bv2Nat : bitvector.
Hint Rewrite Nat.double_twice Nat.div2_succ_double Nat.div2_double
     Nat.add_1_r Nat.add_0_r
  : bitvector.
Hint Rewrite N2Nat.inj_double N2Nat.inj_succ_double
     N2Nat.inj_succ N2Nat.inj_add N2Nat.inj_mul N2Nat.inj_sub
     N2Nat.inj_pred N2Nat.inj_div2 N2Nat.inj_max N2Nat.inj_min
     N2Nat.id
     : bitvector.

Lemma iter_id : forall A n x, Nat.iter n (@id A) x = x.
  induction n; trivial.
Qed.

Lemma iter_0 : forall A (f : A -> A)(x : A) , Nat.iter 0 f x = x.
  intros. trivial.
Qed.

Hint Resolve iter_id.
Hint Resolve iter_0.

Lemma shiftin_cons : forall sz b0 b1 (vec : Bvector sz),
    Vector.tl (Vector.shiftin b0 (b1 :: vec)) = Vector.shiftin b0 vec.
Proof.
  intros. induct_on sz.
Qed.


Lemma N_shiftin_false : forall sz (vec : Bvector sz),
    @Bv2N _ (Vector.shiftin false vec) = Bv2N _ vec.
Proof.
  intros sz vec. induct_on sz.
Qed.

Hint Rewrite N_shiftin_false : bitvector.

Lemma shiftin_false : forall sz (vec : Bvector sz), Bv2Nat (Vector.shiftin false vec) = Bv2Nat vec.
Proof.
  unfold Bv2Nat.
  intros sz vec. crush.
Qed.


Lemma Bv2Nat_shiftR_1 : forall sz b (vec : Bvector sz),
    Bv2Nat (BVshiftR1 (b :: vec)) = Bv2Nat vec.
Proof.
  unfold Bv2Nat.
  intros sz b vec.
  induct_on vec.
Qed.

Hint Rewrite Bv2Nat_shiftR_1 : bitvector.

(*
Lemma Bv2Nat_shiftR_S_n : forall sz (vec : Bvector sz) n b,
    Bv2Nat (BVshiftR (S n) (b :: vec)) = Bv2Nat (BVshiftR n vec).
Proof.
  intros sz vec n.


  induction vec. intro n. induction n. destruct b; try compute; trivial.


Qed.
*)





Lemma Bv2Nat_shiftR_1_div : forall sz (vec : Bvector sz), Bv2Nat (BVshiftR1 vec) = Nat.div2 (Bv2Nat vec).
Proof.
  intros sz vec.
  induction vec; crush;
    unfold BshiftRl; unfold Bhigh;
      rewrite shiftin_cons; rewrite shiftin_false;
        unfold Bv2Nat.
  destruct h;
  crush.
Qed.

Hint Rewrite Bv2Nat_shiftR_1_div : bitvector.
Lemma inj_shiftR : forall sz n (vec : Bvector sz), Bv2Nat (BVshiftR n vec) = Nat.shiftr (Bv2Nat vec) n.
  intros sz n vec.
  unfold BVshiftR.
  induct_on n.
Qed.

Lemma Bv2Nat_shiftR : forall sz n (vec : Bvector sz), Bv2Nat (BVshiftR n vec) = Bv2Nat vec / 2^n.
  intros sz n vec.
  rewrite inj_shiftR.
  apply Nat.shiftr_div_pow2.
Qed.
