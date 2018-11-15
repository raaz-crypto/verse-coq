Require Import Word.

Require Import Vector.
Require Import CoLoR_VecUtil.

Require Import Equality.

Import BOps.

Set Implicit Arguments.


Definition Distr T f g := forall a b c : T,
    g a (f b c) = f (g a b) (g a c).

Definition Comm T (f : T -> T -> T) := forall a b, f a b = f b a.

Arguments Distr [T] f g.
Arguments Comm [T] _.

Section Basics.

  Variable f g : bool -> bool -> bool.
  Variable n : nat.

  Lemma liftDistr : Distr f g -> Distr (@liftBV2 (@Vmap2 _ _ _ f) n)
                                       (@liftBV2 (@Vmap2 _ _ _ g) n).
    unfold Distr.
    intros.
    destruct a, b, c.
    unfold Bvector.Bvector in *.
    simpl.
    f_equal.
    induction n.
    now VOtac.
    VSntac b0. VSntac b1. VSntac b.
    simpl.
    f_equal.
    apply H.
    apply IHn0.
  Qed.

  Lemma liftComm : Comm f -> Comm (@liftBV2 (@Vmap2 _ _ _ f) n).
    unfold Comm.
    intros.
    destruct a, b.
    unfold Bvector.Bvector in *.
    simpl.
    f_equal.
    induction n.
    now VOtac.
    VSntac b0. VSntac b.
    simpl.
    f_equal.
    apply H.
    apply IHn0.
  Qed.

End Basics.

Lemma ntimesCompose A (f : A -> A) n1 n2 a
  : ntimes f n1 (ntimes f n2 a) = ntimes f (n1 + n2) a.
  induction n1.
  trivial.
  simpl.
  f_equal.
  apply IHn1.
Qed.

Lemma OrComm n (w1 w2 : Word.t n)
  : OrW w1 w2 = OrW w2 w1.
  unfold OrW, BVOr.
  apply liftComm.
  unfold Comm.
  apply Bool.orb_comm.
Qed.

Lemma AndComm n (w1 w2 : Word.t n)
  : AndW w1 w2 = AndW w2 w1.
  unfold AndW, BVAnd.
  apply liftComm.
  unfold Comm.
  apply Bool.andb_comm.
Qed.

Lemma OrDistrAnd n (w1 w2 w3 : Word.t n)
  : OrW w1 (AndW w2 w3) = AndW (OrW w1 w2) (OrW w1 w3).
  unfold OrW, BVOr, BVAnd.
  apply liftDistr.
  unfold Distr.
  apply Bool.orb_andb_distrib_r.
Qed.

Lemma AndDistrOr n (w1 w2 w3 : Word.t n)
  : AndW w1 (OrW w2 w3) = OrW (AndW w1 w2) (AndW w1 w3).
  unfold OrW, BVOr, BVAnd.
  apply liftDistr.
  unfold Distr.
  apply Bool.andb_orb_distrib_r.
Qed.

Lemma rotRCompose n r1 r2 (w : Word.t n)
  : RotRW r1 (RotRW r2 w) = RotRW (r1 + r2) w.
Proof.
  destruct w.
  unfold RotRW.
  simpl liftBV.
  f_equal.
  unfold BRotR.
  apply ntimesCompose.
Qed.

Lemma rotRDistrXor n : forall (w1 w2 : Word.t n) r,
    RotRW r (XorW w1 w2) = XorW (RotRW r w1) (RotRW r w2).
Proof.
  destruct w1 as [ b1 ].
  destruct w2 as [ b2 ].
  intro r.
  unfold RotRW.
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
