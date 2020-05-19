Require Import BinNat.
Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.
(* begin hide *)
Hint Rewrite andb_true_r  orb_false_r : bitvector.
Hint Rewrite
     Nat.sub_0_r Nat.sub_diag Nat.mod_0_l Nat.mod_mod
     Nat.double_twice Nat.div2_succ_double Nat.div2_double
     Nat.add_1_r Nat.add_0_r
  : bitvector.

Hint Rewrite
     N.sub_0_r N.sub_diag N.mod_0_l N.mod_mod
     N.div2_succ_double N.div2_double
     N.add_1_r N.add_0_r
  : bitvector.

Hint Rewrite
     Nat2N.inj_double Nat2N.inj_succ Nat2N.inj_succ_double
     Nat2N.inj_succ Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub
     Nat2N.inj_pred Nat2N.inj_div2 Nat2N.inj_max Nat2N.inj_min
     Nat2N.id
     : bitvector.

Hint Rewrite N2Nat.inj_double N2Nat.inj_succ N2Nat.inj_succ_double
     N2Nat.inj_succ N2Nat.inj_add N2Nat.inj_mul N2Nat.inj_sub
     N2Nat.inj_pred N2Nat.inj_div2 N2Nat.inj_max N2Nat.inj_min
     N2Nat.id
     : bitvector.

Hint Resolve
     andb_comm andb_assoc andb_orb_distrib_r
     orb_comm orb_assoc orb_andb_distrib_r
     xorb_comm xorb_assoc
: bitvector.

Hint Unfold BVshiftR BVshiftL : bitvector.

Module Internal.
  Lemma vector_0_nil : forall A (vec : Vector.t A 0), vec = [].
  Proof.
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


  Lemma iter_id : forall A n x, Nat.iter n (@id A) x = x.
    induction n; trivial.
  Qed.



  Lemma iter_0 : forall A (f : A -> A)(x : A) , Nat.iter 0 f x = x.
    intros. trivial.
  Qed.

  Lemma iter_add : forall A (f : A -> A) m n a0, Nat.iter m f (Nat.iter n f a0) = Nat.iter (m+n) f a0.
  Proof.
    intros A f m n a0.
    induction m as [|k IHk]; simpl; trivial.
    rewrite IHk; trivial.
  Qed.

End Internal.

Import Internal.

(* end hide *)

Ltac crush := repeat (
                  unfold arithm;
                  try autorewrite with bitvector; simpl; try eauto with bitvector;
                    match goal with
                    | [ v : Bvector 0     |- _ ] => rewrite (vector_0_nil _ v)
                    | [ |- _ :: _ = _ :: _ ] => apply vector_cons_equation
                    | [ v : Bvector (S _) |- _ ]
                      => rewrite (Vector.eta v);
                        let h := fresh "h" in
                        let t := fresh "t" in
                        (generalize (Vector.hd v) as h;
                         generalize (Vector.tl v) as tl; intros h t)
                    | [ b : bool |- _ ] => destruct b
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

(** * Facts about shifts *)

(** ** Left shifts *)

Lemma BVshiftL_0 : forall sz (vec : Bvector sz),
  BVshiftL 0 vec = vec.
Proof.
  trivial.
Qed.

Lemma BVshiftL_add_m_n : forall sz (vec : Bvector sz) n m,
  BVshiftL n (BVshiftL m vec) = BVshiftL (n + m) vec.
Proof.
  intros sz vec n m.
  induct_on n.
Qed.


Lemma BVshiftL_commute : forall sz  (vec : Bvector sz) m n,
  BVshiftL m (BVshiftL n vec) = BVshiftL n (BVshiftL m vec).
Proof.
  intros. autorewrite with bitvector.
  repeat rewrite BVshiftL_add_m_n.
  rewrite Nat.add_comm; trivial.
Qed.

Lemma BVshiftL_assoc : forall sz (vec : Bvector sz) m n p,
  (fun v => BVshiftL m (BVshiftL n v)) (BVshiftL p vec) = BVshiftL m (BVshiftL n (BVshiftL p vec)).
Proof.
  intros; crush.
Qed.

(** ** Right shifts *)

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

Lemma BVshiftR_commute : forall sz  (vec : Bvector sz) m n,
  BVshiftR m (BVshiftR n vec) = BVshiftR n (BVshiftR m vec).
Proof.
  intros; autorewrite with bitvector.
  repeat rewrite BVshiftR_add_m_n.
  rewrite Nat.add_comm; trivial.
Qed.

Lemma BVshiftR_assoc : forall sz (vec : Bvector sz) m n p,
  (fun v => BVshiftR m (BVshiftR n v)) (BVshiftR p vec) = BVshiftR m (BVshiftR n (BVshiftR p vec)).
Proof.
  intros; crush.
Qed.


(* begin hide *)
Module ShiftInternal.
  (**
      Internal lemma that might not be of interest outside this module.
   *)
  Lemma shiftin_cons : forall sz b0 b1 (vec : Bvector sz),
    Vector.tl (Vector.shiftin b0 (b1 :: vec)) = Vector.shiftin b0 vec.
  Proof.
    intros. induct_on sz.
  Qed.


  Lemma shiftin_false : forall sz (vec : Bvector sz),
      @Bv2N _ (Vector.shiftin false vec) = @Bv2N _ vec.
  Proof.
    intros sz vec. induct_on sz.
  Qed.

  Hint Rewrite shiftin_false : bitvector.


  Lemma Bv2N_shiftR_1 : forall sz b (vec : Bvector sz),
      Bv2N (BVshiftR1 (b :: vec)) = Bv2N vec.
  Proof.
    intros sz b vec.
    induct_on vec.
  Qed.

  Hint Rewrite Bv2N_shiftR_1 : bitvector.


  Lemma Bv2N_shiftR_1_div : forall sz (vec : Bvector sz), Bv2N (BVshiftR1 vec) = N.div2 (Bv2N vec).
  Proof.
    intros sz vec.
    Hint Rewrite shiftin_cons shiftin_false : bitvector.
    induction vec. crush.
    simpl. unfold BshiftRl; unfold Bhigh.
    crush.
  Qed.

  Hint Rewrite Bv2N_shiftR_1_div : bitvector.

  Lemma inj_shiftR : forall sz n (vec : Bvector sz),
      Bv2N (BVshiftR n vec) = N.shiftr (Bv2N vec) (N.of_nat n).
  Proof.
    intros sz n vec.
    unfold BVshiftR.
    Hint Rewrite N.shiftr_succ_r : bitvector.
    induct_on n.
  Qed.

End ShiftInternal.

Import ShiftInternal.


Lemma Bv2N_shiftR : forall sz n (vec : Bvector sz), Bv2N (BVshiftR n vec) = (Bv2N vec / 2^N.of_nat n)%N.
  intros sz n vec.
  rewrite inj_shiftR.
  apply N.shiftr_div_pow2.
Qed.



(** * And and Or *)
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
Proof.
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

(* ** Distributivity *)

Lemma BVor_and_distrib :
  forall sz (v1 v2 v3 : Bvector sz),
    BVor v1 (BVand v2 v3) = BVand (BVor v1 v2) (BVor v1 v3).
Proof.
  intros sz v1 v2 v3.
  induct_on sz.
Qed.

Lemma BVand_or_distrib :
  forall sz (v1 v2 v3 : Bvector sz),
    BVand v1 (BVor v2 v3) = BVor (BVand v1 v2) (BVand v1 v3).
Proof.
  intros sz v1 v2 v3.
  induct_on sz.
Qed.

(** * Lemma on xor *)
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


(** * Rotation lemma *)
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
Proof.
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

(** * Bitvector arithmetic proofs *)

(** injectivity of Bv2N function *)

Lemma inj : forall sz (v0 v1 : Bvector sz),  Bv2N v0 = Bv2N v1 -> v0 = v1.
Proof.
  intros sz v0 v1.
  intros pfBv2NEq.
  pose (f_equal (N2Bv_sized sz) pfBv2NEq) as Hyp.
  repeat rewrite N2Bv_sized_Bv2N in Hyp.
  trivial.
Qed.

Module ArithmInternals.

  Lemma N2Bv_sized_0 : forall x, N2Bv_sized 0 x = [].
  Proof.
    now (intros; destruct x; compute).
  Qed.


  Lemma N2Bv_sized_succ : forall sz x, N2Bv_sized (S sz) x = N.odd x  :: (N2Bv_sized sz (N.div2 x)).
  Proof.
    intros sz x.
    destruct x as [|pos]. simpl; f_equal.
    destruct pos;  simpl; f_equal.
  Qed.


  Lemma Bv2N_cons : forall sz b (vec : Bvector sz), Bv2N  (b :: vec) = ((N.b2n b) + 2 * Bv2N vec)%N.
  Proof.
    intros sz b vec.
    simpl.
    destruct b.
    destruct (Bv2N vec); trivial.
    destruct (Bv2N vec); trivial.
  Qed.

  Lemma pow_2_nonzero : forall x, (2^x <> 0)%N.
  Proof.
    intro.
    apply N.pow_nonzero.
    intro twoEq0; inversion twoEq0.
  Qed.



  Lemma nonzero_2 : (2 <> 0)%N.
    intro Hyp; inversion Hyp.
  Qed.
  Hint Resolve pow_2_nonzero nonzero_2 : bitvector.

  Lemma Bv2N_false : forall m, Bv2N (Bvect_false m) = 0%N.
  Proof.
    intro m.
    induct_on m.
  Qed.

  Lemma Nb2n_mod : forall x, (N.b2n(N.odd x) = x mod 2)%N.
  Proof.
    intro x.
    rewrite <- N.bit0_mod.
    f_equal.
    auto using N.bit0_odd.
  Qed.

  Lemma Bv2N_N2Bv_sized_mod  : forall sz x, Bv2N (N2Bv_sized sz x) = (x mod 2^N.of_nat sz)%N.
  Proof.
    Hint Rewrite
         N2Bv_sized_0 N2Bv_sized_succ
         N.mod_1_r Bv2N_cons
         N.div2_div
         N.pow_succ_r
         N.mod_mul_r : bitvector.

    Hint Resolve Nb2n_mod N.le_0_l : bitvector.
    intro sz.
    induction sz as [|n IHsz]. intro x; crush.
    intro x; autorewrite with bitvector; eauto with bitvector.
    rewrite IHsz;
      rewrite N.add_cancel_r;
    crush.

  Qed.

End ArithmInternals.

Import ArithmInternals.
Hint Resolve Bv2N_N2Bv_sized_mod : bitvector.

Lemma Bv2N_plus : forall sz (v0 v1 : Bvector sz),
    (Bv2N (BVplus v0 v1) = (Bv2N v0 + Bv2N v1) mod 2^(N.of_nat sz))%N.
Proof.
  unfold BVplus.
  intros.
  crush.
Qed.
