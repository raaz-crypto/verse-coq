Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.
Require Import Verse.BitVector.Facts.

Hint Unfold  Bv2Nat : bitvector.
Hint Rewrite Nat.add_1_r        : bitvector.
Hint Rewrite Nat.add_0_r        : bitvector.
Hint Rewrite Nat.double_twice   : bitvector.


Hint Rewrite Nat.double_twice Nat.div2_succ_double Nat.div2_double : Nnat.

Hint Rewrite Nat2N.inj_double Nat2N.inj_succ_double
     Nat2N.inj_succ Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub
     Nat2N.inj_pred Nat2N.inj_div2 Nat2N.inj_max Nat2N.inj_min
     Nat2N.id
  : natN.


Ltac crush := repeat (simpl; trivial;
                      autorewrite with bitvector;  eauto;
                      match goal with
                      | [ |- _ -> _ ]   => intro
                      | [ b : bool |- _ ] => destruct b
                      | [ |- Vector.t _ _ -> _] => intro
                      | [ |- N.to_nat _ = _ ] => autorewrite with Nnat
                      | [ |- N.of_nat _ = _ ] => autorewrite with natN
                      | _ =>  idtac
                      end).

Ltac induct_crush n :=
  induction n as [|n IHn]; crush; rewrite IHn; crush.


Lemma iter_id : forall A n x, Nat.iter n (@id A) x = x.
  induction n; trivial.
Qed.

Lemma iter_0 : forall A (f : A -> A)(x : A) , Nat.iter 0 f x = x.
  intros. trivial.
Qed.

Hint Resolve iter_id.
Hint Resolve iter_0.

Lemma shiftin_cons : forall n b0 b1 (vec : Bvector n), Vector.tl (Vector.shiftin b0 (b1 :: vec))
                                                  = Vector.shiftin b0 vec.
  intros.
  induction vec; crush.
Qed.


Lemma N_shiftin_false : forall n (vec : Bvector n), @Bv2N _ (Vector.shiftin false vec) = @Bv2N _ vec.
  intro n; intro vec; induction vec; trivial.
  simpl. crush; rewrite IHvec; trivial.
Qed.


Lemma shiftin_false : forall n (vec : Bvector n), Bv2Nat (Vector.shiftin false vec) = Bv2Nat vec.
  unfold Bv2Nat. intros; rewrite N_shiftin_false.  trivial.
Qed.

Lemma Bv2Nat_shiftR_1 : forall sz (vec : Bvector sz), Bv2Nat (BVshiftR1 vec) = Nat.div2 (Bv2Nat vec).
  intros sz vec.
  induction vec; simpl; trivial.
  unfold BshiftRl. unfold Bhigh.
  rewrite shiftin_cons. rewrite shiftin_false.
  destruct h; unfold Bv2Nat;  crush.
Qed.


Lemma inj_shiftR : forall sz n (vec : Bvector sz), Bv2Nat (BVshiftR n vec) = Nat.shiftr (Bv2Nat vec) n.
  intros sz n vec.
  unfold BVshiftR.
  induction n; eauto.
  simpl.
  rewrite Bv2Nat_shiftR_1.
  eauto.
Qed.

Lemma Bv2Nat_shiftR : forall sz n (vec : Bvector sz), Bv2Nat (BVshiftR n vec) = Bv2Nat vec / 2^n.
  intros sz n vec.
  rewrite inj_shiftR.
  apply Nat.shiftr_div_pow2.
Qed.


(*


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
  intros b c y; crush.
Qed.

Hint Rewrite N2Nat_inj_if : bitvector.

(*
Lemma BVshiftR_S_n_r : forall sz n (vec : Bvector sz), BVshiftR (S n) vec = BVshiftR n (BVshiftR 1 vec).
  intros sz n.
  induction n.
  intro vec. rewrite BVshiftR_0; trivial.
  intro vec.
  rewrite IHn.
  rewrite BVshiftR_S_n_l.

  induction vec. simpl; trivial.

Qed.

Lemma BVshiftR_nil : forall n (vec : Bvector 0), BVshiftR n vec = vec.
  intros n vec.
  crush.
Qed.



Hint Rewrite shiftin_cons : bitvector.
Hint Rewrite shiftin_false_lemma_N : bitvector.


Hint Rewrite shiftin_false_lemma.
Hint Resolve shiftin_false_lemma : core.

Lemma Bv2Nat_shiftR_cons : forall sz b (vec : Bvector sz),
    Bv2Nat (BVshiftR 1 (b :: vec)) = Bv2Nat vec.
  intros sz b vec.
  unfold BVshiftR. simpl.
  unfold BshiftRl.
  unfold Bhigh. rewrite shiftin_cons.
  crush.
Qed.


Lemma Bv2Nat_cons_false : forall sz (vec : Bvector sz), Bv2Nat (false :: vec) = Nat.double (Bv2Nat vec).
  unfold Bv2Nat. crush.
Qed.

Lemma Bv2Nat_cons_true : forall sz (vec : Bvector sz), Bv2Nat (true :: vec) = S (Nat.double (Bv2Nat vec)).
  unfold Bv2Nat. crush.
Qed.


Lemma Bv2Nat_shiftR_S_n : forall sz  (vec : Bvector sz) b n,
    Bv2Nat (BVshiftR (S n) (b :: vec)) = Bv2Nat (BVshiftR n vec).

  intros sz vec.
  intros b.
  intros n.
  induction n. rewrite Bv2Nat_shiftR_cons; rewrite BVshiftR_0; trivial.
  destruct b.

  (*induction sz. rewrite (vector_0_nil _ vec).
  destruct b.*)
  induction n.
  intro vec.
  rewrite Bv2Nat_shiftR_cons. rewrite BVshiftR_0. trivial.
  intro vec.
  rewrite BVshiftR_S_n.


  simpl. unfold BshiftRl.
  unfold Bhigh.
  rewrite shiftin_false_lemma.
  rewrite BVshiftR_0; trivial.
  rewrite BVshift
  induction vec.

  rewrite BVshiftR_0.

  simpl.



Hint Resolve N.div2_succ_double : core.
Hint Resolve N.div2_double : core.

Lemma  Ndiv2_cons :  forall sz b (vec : Bvector sz), N.div2 (Bv2N (b :: vec)) = Bv2N vec.
  intros n b.
  destruct b; simpl Bv2N; eauto.
Qed.



Lemma Natdiv2_cons  : forall sz b (vec : Bvector sz), Nat.div2 (Bv2Nat (b :: vec)) = Bv2Nat vec.
  intros.
  unfold Bv2Nat.
  rewrite <- N2Nat.inj_div2.
  rewrite Ndiv2_cons; trivial.
Qed.

Hint Rewrite Bv2Nat_cons_false : bitvector.
Hint Rewrite Bv2Nat_cons_true  : bitvector.


Module Bv2Nat.


  Definition inj_shfitr : forall sz n (vec : Bvector (S sz)),
    Bv2Nat (BVshiftR n vec) = Nat.shiftr (Bv2Nat vec) n.
   intros sz n vec.
   induction n. simpl; trivial.
   simpl Nat.shiftr.
   rewrite (Vector.eta vec).
   generalize (Vector.hd vec).
   intro b.
   destruct b.
   rewrite <- IHn.

   try rewrite Bv2Nat_cons_true; try rewrite Bv2Nat_cons_false.


Print Vector.shiftin.

Hint Rewrite shiftin_false_lemma : bvector.
Hint Resolve shiftin_false_lemma : core.


Hint Rewrite Ndiv2_cons.
Lemma shiftR_div2 : forall n (vec : Bvector (S n)), Bv2N (BshiftRl n vec false) = N.div2 (Bv2N vec).
  intro n.
  induction n; intro vec; rewrite (Vector.eta vec).
  generalize (Vector.hd vec). crush.
  unfold BshiftRl. simpl Vector.shiftin. rewrite Ndiv2_cons.
  simpl.
  eauto.
Qed.

Le

Search N.div2.

Lemma Nat_iterdiv : forall n x : N, N.iter n (N.div2) x = (x / 2^n)%N.



Lemma div2power_nat_spec_np :  forall (n p : nat) (vec : Bvector (n + p)),
    Bv2Nat (div2power_nat n vec) = Bv2Nat vec mod 2^n.
  unfold Bv2Nat.
  unfold div2power_nat.
  intros n p.
  induction p. crush.
  induction vec. trivial.

Abort.

*).
*)
