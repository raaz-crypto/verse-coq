Require Import Word.

Require Import Vector.
Require Import CoLoR_VecUtil.

Require Import Equality.

Import BOps.

Lemma ntimesCompose A (f : A -> A) n1 n2 a
  : ntimes f n1 (ntimes f n2 a) = ntimes f (n1 + n2) a.
  induction n1.
  trivial.
  simpl.
  f_equal.
  apply IHn1.
Qed.

Lemma rotRCompose n r1 r2 (w : Word.t n)
  : RotR r1 (RotR r2 w) = RotR (r1 + r2) w.
Proof.
  destruct w.
  unfold RotR.
  simpl liftBV.
  f_equal.
  unfold BRotR.
  apply ntimesCompose.
Qed.

Lemma rotRDistrXor n : forall (w1 w2 : Word.t n) r,
    RotR r (w1 (XOR) w2) = RotR r w1 (XOR) RotR r w2.
  (*
Lemma rotRDistrXor n : forall (b1 b2 : Bvector.Bvector (S n)) r,
    BRotR r (BVXor b1 b2) = BVXor (BRotR r b1) (BRotR r b2).*)
Proof.
  destruct w1 as [ b1 ].
  destruct w2 as [ b2 ].
  intro r.
  unfold RotR.
  unfold XorW.
  cbn [liftBV liftBV2].
  f_equal.
  (* Reduced to assertion on BVectors *)
  induction r.
  - unfold BRotR; trivial.
  - unfold BRotR.
    unfold Word.BOps.ntimes.
    fold Word.BOps.ntimes.
    fold (BRotR r (BVXor b1 b2)).
    fold (BRotR r b1).
    fold (BRotR r b2).
    rewrite IHr.
    generalize (BRotR r b1) as bv1.
    generalize (BRotR r b2) as bv2.
    (* Reduced to the single rotation case *)
    clear IHr.
    intros.
    destruct n.
    simpl; trivial.
    VSntac (Vmap2 xorb bv1 bv2).
    VSntac bv1. VSntac bv2.
    simpl.
    (* This assertion does not have an induction by n proof *)
    f_equal.
    * destruct n.
      assert (Vtail bv1 = Vnil).
      apply VO_eq.
      rewrite H2.
      assert (Vtail bv2 = Vnil).
      apply VO_eq.
      rewrite H3.
      trivial.

      assert (n < S n) by auto.
      repeat rewrite (Vlast_nth _ _ H2).
      unfold BVXor.
      rewrite Vnth_map2; trivial.
    * unfold BVXor.
      unfold Vmap2 at 1.
      fold (Vmap2 xorb bv1 bv2).
      rewrite <- H0.
      rewrite <- H1.
      (* Finally down to an assertion that can be proved by induction on n *)
      clear b1 b2 r H H0 H1.
      induction n.
      + apply VO_eq.
      + VSntac bv1. VSntac bv2.

        unfold Vremove_last at 1.
        simpl.
        f_equal.
        (* Now to rewrite to look like induction hypothesis *)
        repeat rewrite Vsub_cons.
        unfold Vmap2 at 1.
        fold (Vmap2 xorb (Vtail bv1) (Vtail bv2)).
        rewrite (Vsub_pi (Vremove_last_aux n)).
        fold (Vremove_last (Vmap2 xorb (Vtail bv1) (Vtail bv2))).
        rewrite (Vsub_pi (Vremove_last_aux n)).
        fold (Vremove_last (Vtail bv1)).
        rewrite (Vsub_pi (Vremove_last_aux n)).
        fold (Vremove_last (Vtail bv2)).

        apply IHn.
Qed.
