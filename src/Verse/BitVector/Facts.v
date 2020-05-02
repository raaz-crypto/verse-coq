Require Import BinNat.
Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.

Hint Unfold BVshiftR BVshiftL : bitvector.

Lemma vector_0_nil : forall A (vec : Vector.t A 0), vec = [].
  intro A.
  exact (Vector.case0 (fun v => v = []) eq_refl).
Qed.
Ltac crush := repeat (simpl; eauto with bitvector;
                      match goal with
                      | [ |- bool -> _ ] => intro
                      | [b : bool |- _ ] => destruct b
                      | [ v : Bvector 0     |- _ ] => rewrite (vector_0_nil _ v)
                      | [ v : Bvector (S _) |- _ ]
                        => rewrite (Vector.eta v);
                          let h := fresh "h" in
                          let t := fresh "t" in
                          (generalize (Vector.hd v) as h;
                           generalize (Vector.tl v) as tl; intros h t)

                      | [ v : _ |- context[Vector.hd ?v] ] => generalize (Vector.hd v)
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
  induction n as [|m IHm]; crush; rewrite IHm; crush.

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

Lemma BVand_commute : forall sz (v1 v2 : Bvector sz), BVand v1 v2 = BVand v2 v1.
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


Lemma BVor_commute : forall sz (v1 v2 : Bvector sz), BVor v1 v2 = BVor v2 v1.
Proof.
  intros sz v1 v2.
  induct_on sz.
Qed.

Lemma BVor_assoc : forall sz (v1 v2 v3 : Bvector sz), BVor v1 (BVor v2 v3) = BVor (BVor v1 v2) v3.
  intros sz v1 v2 v3.
  induct_on sz.
Qed.
