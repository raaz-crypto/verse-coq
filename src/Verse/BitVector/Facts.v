Require Import BinNat.
Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.

Hint Unfold BVshiftR BVshiftL : bitvector.


Ltac crush := repeat (simpl; eauto with bitvector).
Ltac induct_on n :=
  let m := fresh "m" in
  let IHm := fresh "IHm" in
  induction n as [|m IHm]; crush; rewrite IHm; crush.


Lemma BVshiftR_add_m_n : forall sz (vec : Bvector sz) n m,
    BVshiftR n (BVshiftR m vec) = BVshiftR (n + m) vec.

  intros sz vec n m.
  induct_on n.
Qed.

Lemma BVshiftL_add_m_n : forall sz (vec : Bvector sz) n m,
    BVshiftL n (BVshiftL m vec) = BVshiftL (n + m) vec.

  intros sz vec n m.
  induct_on n.
Qed.

Hint Rewrite BVshiftL_add_m_n  BVshiftR_add_m_n : bitvector.


Lemma BVshiftR_commute : forall sz  (vec : Bvector sz) m n,
    BVshiftR m (BVshiftR n vec) = BVshiftR n (BVshiftR m vec).
  intros. autorewrite with bitvector.
  rewrite Nat.add_comm; trivial.
Qed.

Lemma BVshiftL_commute : forall sz  (vec : Bvector sz) m n,
    BVshiftL m (BVshiftL n vec) = BVshiftL n (BVshiftL m vec).
  intros. autorewrite with bitvector.
  rewrite Nat.add_comm; trivial.
Qed.

Hint Resolve BVshiftR_add_m_n : bitvector.
Hint Resolve BVshiftR_commute : bitvector.
