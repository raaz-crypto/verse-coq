Require Import BinNat.
Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.

Hint Rewrite andb_true_r  orb_false_r : bitvector.
Hint Resolve
     andb_comm andb_assoc
     orb_comm orb_assoc
     xorb_comm xorb_assoc
  : bitvector.
Hint Rewrite Nat.sub_0_r Nat.sub_diag Nat.mod_0_l Nat.mod_mod : bitvector.
Hint Unfold BVshiftR BVshiftL : bitvector.
Hint Unfold Bv2Nat :bitvector.

Lemma vector_0_nil : forall A (vec : Vector.t A 0), vec = [].
  intro A.
  exact (Vector.case0 (fun v => v = []) eq_refl).
Qed.

Lemma vector_cons_equation {A} {a1 a2 : A} {n} {v1 v2 : Vector.t A n}:
  a1 = a2 -> v1 = v2 -> a1 :: v1 = a2 :: v2.
Proof.
  intros H1 H2.
  rewrite H1. rewrite H2.
  trivial.
Qed.

Ltac crush := repeat (simpl; eauto with bitvector; try autorewrite with bitvector;
                      match goal with
                      | [ v : Bvector 0     |- _ ] => rewrite (vector_0_nil _ v)
                      | [ |- _ :: _ = _ :: _ ] => apply vector_cons_equation
                      | [ v : Bvector (S _) |- _ ]
                        => rewrite (Vector.eta v);
                          let h := fresh "h" in
                          let t := fresh "t" in
                          (generalize (Vector.hd v) as h;
                           generalize (Vector.tl v) as tl; intros h t)
                      | [ |- Vector.map2 _ _ _ = Vector.map2 _ _ _ ]
                        => rewrite <- Vector.eq_nth_iff
                      | _ => idtac
                      end).

(** A more powerful induction

1. Apply induction on the given variable

2. Base case is crushed

3. The induction step is first softened by a crush then a rewrite by the Inductive hypothesis
   followed by crush.


*)

Ltac induct_on n :=
  let m := fresh "m" in
  let IHm := fresh "IHm" in
  (induction n as [|m IHm]; crush; rewrite IHm; crush).

(** The vector variant of the induction *)
Ltac induct_on_vec v :=
  let b := fresh "b" in
  let sz := fresh "sz" in
  let vec := fresh "vec" in
  let IHvec := fresh "IHvec" in
  (induction v as [|b sz vec IHvec]; crush; rewrite IHvec; crush).

Lemma iter_add : forall A (f : A -> A) m n a0, Nat.iter m f (Nat.iter n f a0) = Nat.iter (m+n) f a0.
Proof.
  intros A f m n a0.
  induct_on m.
Qed.


Lemma BVshiftL_0 : forall sz (vec : Bvector sz),
    BVshiftL 0 vec = vec.
Proof.
  trivial.
Qed.

Lemma BVshiftR_0 : forall sz (vec : Bvector sz),
    BVshiftR 0 vec = vec.
Proof.
  trivial.
Qed.

Lemma BVshiftR_add_m_n : forall sz (vec : Bvector sz) n m,
    BVshiftR n (BVshiftR m vec) = BVshiftR (n + m) vec.
Proof.
  intros sz vec n m.
  induct_on n.
Qed.

Lemma BVshiftL_add_m_n : forall sz (vec : Bvector sz) n m,
    BVshiftL n (BVshiftL m vec) = BVshiftL (n + m) vec.
Proof.
  intros sz vec n m.
  induct_on n.
Qed.

Hint Rewrite BVshiftL_add_m_n  BVshiftR_add_m_n : bitvector.


Lemma BVshiftR_commute : forall sz  (vec : Bvector sz) m n,
    BVshiftR m (BVshiftR n vec) = BVshiftR n (BVshiftR m vec).
Proof.
  intros; autorewrite with bitvector.
  rewrite Nat.add_comm; trivial.
Qed.

Lemma BVshiftR_assoc : forall sz (vec : Bvector sz) m n p,
    (fun v => BVshiftR m (BVshiftR n v)) (BVshiftR p vec) = BVshiftR m (BVshiftR n (BVshiftR p vec)).
Proof.
  intros; crush.
Qed.

Lemma BVshiftL_commute : forall sz  (vec : Bvector sz) m n,
    BVshiftL m (BVshiftL n vec) = BVshiftL n (BVshiftL m vec).
Proof.
  intros. autorewrite with bitvector.
  rewrite Nat.add_comm; trivial.
Qed.

Lemma BVshiftL_assoc : forall sz (vec : Bvector sz) m n p,
    (fun v => BVshiftL m (BVshiftL n v)) (BVshiftL p vec) = BVshiftL m (BVshiftL n (BVshiftL p vec)).
Proof.
  intros; crush.
Qed.

Hint Resolve BVshiftR_add_m_n : bitvector.
Hint Resolve BVshiftR_commute : bitvector.

Lemma BVand_0_r : forall sz (v  : Bvector sz), BVand v BVones = v.
Proof.
  intros sz v.
  induct_on sz.
Qed.

Lemma BVand_0_l : forall sz (v  : Bvector sz), BVand BVones v = v.
Proof.
  intros sz v.
  induct_on sz.
Qed.

Lemma BVand_comm : forall sz (v1 v2 : Bvector sz), BVand v1 v2 = BVand v2 v1.
Proof.
  intros sz v1 v2.
  induct_on sz.
Qed.

Lemma BVand_assoc : forall sz (v1 v2 v3 : Bvector sz), BVand v1 (BVand v2 v3) = BVand (BVand v1 v2) v3.
  intros sz v1 v2 v3.
  induct_on sz.
Qed.

Lemma BVor_0_r : forall sz (v  : Bvector sz), BVor v BVzeros = v.
Proof.
  intros sz v.
  induct_on sz.
Qed.

Lemma BVor_0_l : forall sz (v  : Bvector sz), BVor BVzeros v = v.
Proof.
  intros sz v.
  induct_on sz.
Qed.


Lemma BVor_comm : forall sz (v1 v2 : Bvector sz), BVor v1 v2 = BVor v2 v1.
Proof.
  intros sz v1 v2.
  induct_on sz.
Qed.

Lemma BVor_assoc : forall sz (v1 v2 v3 : Bvector sz), BVor v1 (BVor v2 v3) = BVor (BVor v1 v2) v3.
Proof.
  intros sz v1 v2 v3.
  induct_on sz.
Qed.

Lemma BVxor_comm : forall sz (v1 v2 : Bvector sz), BVxor v1 v2 = BVxor v2 v1.
Proof.
  intros sz v1 v2.
  induct_on sz.
Qed.


Lemma BVxor_assoc : forall sz (v1 v2 v3 : Bvector sz), BVxor v1 (BVxor v2 v3) = BVxor (BVxor v1 v2) v3.
Proof.
  intros sz v1 v2 v3.
  induct_on sz.
Qed.

Lemma BVrotR_0 : forall sz (vec : Bvector sz),
    BVrotR 0 vec = vec.
Proof.
  crush.
Qed.

Lemma BVrotR_add : forall sz m n (vec : Bvector sz),
    BVrotR m (BVrotR n vec) = BVrotR (m + n) vec.
Proof.
  intros.
  unfold BVrotR.
  apply iter_add.
Qed.

Lemma BVrotL_0 : forall sz (vec : Bvector sz),
    BVrotL 0 vec = vec.
Proof.
  trivial.
Qed.

Lemma BVrotL_add : forall sz m n (vec : Bvector sz),
    BVrotL m (BVrotL n vec) = BVrotL (m + n) vec.
Proof.
  intros.
  unfold BVrotL.
  apply iter_add.
Qed.

Lemma popout_shiftin : forall sz x (xs : Bvector sz),
    popout (Vector.shiftin x xs) = (xs,x).
Proof.
  intros sz x xs.
  induct_on_vec xs.
Qed.


Lemma rotMSB_S_n : forall n v, rotTowardsMSB (S n) v = let (xs,x) := popout v in (x :: xs).
Proof.
  intros.
  crush.
Qed.

Lemma rotMSB_LSB_inv : forall sz (v : Bvector sz),
    rotTowardsMSB sz (rotTowardsLSB sz v) = v.
Proof.
  Hint Rewrite rotMSB_S_n popout_shiftin :bitvector.
  Hint Unfold rotTowardsLSB : bitvector.
  intros sz v.
  destruct v; crush.
Qed.

Lemma BVrotL1 : forall sz n (v : Bvector sz), BVrotL 1 (BVrotR (S n) v) = BVrotR n v.
  intros. simpl.
  rewrite rotMSB_LSB_inv.
  trivial.
Qed.

Lemma BVrotRL_inv : forall sz n (v : Bvector sz), BVrotL n (BVrotR n v) = v.
Proof.
  intros sz n v.
  induction n; trivial.
  rewrite <- Nat.add_1_r.
  rewrite <- BVrotL_add.
  rewrite Nat.add_1_r.
  rewrite BVrotL1.
  assumption.
Qed.
