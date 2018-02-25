Require Import Verse.Word.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Syntax.
Require Import Verse.Language.

Require Import Bool.
Require Import Eqdep_dec.
Require Import Equality.
Require Vector.
Require Import VectorEq.


Definition decidable (P:Prop) := {P} + {~ P}.

Definition eq_dec (T : Type) := forall (t1 t2 : T),  decidable (t1 = t2).

Definition nat_eq_dec := NPeano.Nat.eq_dec.

Section DecFacts.

  Variable T : Type.
  Variable T_dec : forall (a b : T), decidable (a = b).

  (* Boolean equality for decidable Types *)
  Definition eqdec_eqb := fun a b => if T_dec a b then true else false.

  Definition eqdec_eqbeq : forall a b, eqdec_eqb a b = true <-> a = b.
    unfold eqdec_eqb. intros.
    destruct (T_dec a b);
      unfold iff; split; first [discriminate | contradiction | trivial].
  Defined.

  (* Vector equality is decidable *)
  Definition vec_eq_dec n : eq_dec (Vector.t T n).
    unfold eq_dec. apply (Vector.eq_dec T eqdec_eqb eqdec_eqbeq).
  Defined.

  (* Equality over existential quantification is decidable *)
  Lemma exists_eq_dec (P : T -> Prop)
        (P_eq_dec : forall (t : T) , eq_dec (P t)) : eq_dec {t : T | P t}.
  Proof.
    Set Keep Proof Equalities.
    unfold eq_dec.
    destruct t1. destruct t2.
    destruct (T_dec x x0). subst. destruct (P_eq_dec _ p p0). subst p0.
    - left; trivial.
    - right; unfold not; intros; injection H;
        intros; pose (inj_pair2_eq_dec _ T_dec _ _ _ _ H0); contradiction.
    - right; congruence.
    Unset Keep Proof Equalities.
  Qed.

  (* Less-than proofs have decidable equality *)
  Axiom lt_unique : forall n m (p q : n < m), p = q.
  Definition lt_eq_dec n m : eq_dec (n < m) := fun p q => left (lt_unique n m p q).

End DecFacts.

(** Decidable equality for Verse constructs *)

Scheme Equality for kind.

Lemma endian_eq_dec : eq_dec endian.
  unfold eq_dec; unfold decidable.
  decide equality.
Qed.

Scheme Equality for align.

Lemma ty_eq_dec : forall {k}, eq_dec (type k).
  unfold eq_dec; unfold decidable.
  destruct k.

  abstract (dependent destruction t1; dependent destruction t2; [try (right; congruence) ..];
            [destruct (nat_eq_dec n n0); [left | right ..]; try congruence |
             destruct (nat_eq_dec n n1), (nat_eq_dec n0 n2); [left | right .. ]; try congruence])
  using directTy_eq_dec.

  dependent destruction t1; dependent destruction t2.
  destruct (align_eq_dec a a0); destruct (nat_eq_dec n n0); destruct (endian_eq_dec e e0); destruct (directTy_eq_dec t1 t2);
    first [ left; congruence | right; congruence ].
Qed.

Lemma bytes_dec : forall (n : nat), eq_dec (bytes n).
  unfold eq_dec; unfold decidable.
  unfold bytes. destruct t1. destruct t2.
  unfold Bvector.Bvector in b, b0.
  pose (vec_eq_dec bool bool_dec (8 * n) b b0) as s.
  destruct s.
  left; apply f_equal; trivial.
  right; unfold not; inversion 1; contradiction.
Qed.

Lemma constant_dec ty : eq_dec (constant ty).
  unfold eq_dec; unfold decidable.
  dependent induction ty;
  simpl; try apply vec_eq_dec; try apply bytes_dec; trivial.
Qed.

Section LanguageDecs.

  Variable v : VariableT.
  Variable v_eq_dec : forall {k} {ty : type k}, eq_dec (v _ ty).

  Arguments v_eq_dec [k ty] _.

  Lemma op_eq_dec {a} : eq_dec (op a).
    unfold eq_dec; unfold decidable.
    destruct a; dependent destruction t1; dependent destruction t2;
      solve [left; congruence |
             right; congruence |
             destruct (nat_eq_dec n n0); solve [left; congruence | right; congruence]
            ].
  Qed.

  Scheme Equality for argKind.

  Lemma arg_eq_dec {ty : type direct} {aK} : eq_dec (arg v aK _ ty).
    unfold eq_dec; unfold decidable.
    dependent destruction t1; dependent destruction t2;
      try (solve [(right; unfold not; inversion 1)]).
    * destruct (v_eq_dec v0 v1); [left; congruence | right];
        unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1); contradiction.
    * destruct (constant_dec ty c c0); [left; congruence | right];
        unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1).
      contradiction.
    * destruct (align_eq_dec a a0);
        destruct (nat_eq_dec b b0);
        destruct (endian_eq_dec e e0);
        subst; [ | right; unfold not; inversion 1; contradiction ..].
      destruct (v_eq_dec x x0); subst; [ | right; unfold not; inversion 1].
      destruct (exists_eq_dec _ nat_eq_dec _ (fun n => lt_eq_dec n b0) i i0);
        [ left; congruence | right ].
      unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ nat_eq_dec _ _ _ _ H1).
      pose (inj_pair2_eq_dec _ endian_eq_dec _ _ _ _ e).
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ e1).
      pose (inj_pair2_eq_dec _ (@v_eq_dec memory (array a0 b0 e0 ty)) _ _ _ _ e2); contradiction.

      pose (inj_pair2_eq_dec _ nat_eq_dec _ _ _ _ H1).
      pose (inj_pair2_eq_dec _ endian_eq_dec _ _ _ _ e).
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ e1); contradiction.
  Defined.

  Definition instruction_eq_dec : eq_dec (instruction v).
    unfold eq_dec; unfold decidable.
    destruct t1 as [a1 | m1 | d1]; destruct t2 as [a2 | m2 | d2]; try (solve [right; inversion 1]).
    - dependent destruction a1; dependent destruction a2; try (solve [right; inversion 1]);
        destruct (ty_eq_dec ty ty0); try (solve [right; inversion 1; contradiction]); subst.
      * destruct (op_eq_dec b b0); try (solve [right; inversion 1; contradiction]).
        destruct (arg_eq_dec l l0); destruct (arg_eq_dec r r1); destruct (arg_eq_dec r0 r2);
          [left; congruence | right; inversion 1 ..].
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H4); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H4); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H4); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
      * destruct (op_eq_dec u u0); try (solve [right; inversion 1; contradiction]).
        destruct (arg_eq_dec l l0); destruct (arg_eq_dec r r0);
          [left; congruence | right; inversion 1 ..].
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
      * destruct (op_eq_dec b b0); try (solve [right; inversion 1; contradiction]).
        destruct (arg_eq_dec l l0); destruct (arg_eq_dec r r0);
          [left; congruence | right; inversion 1 ..].
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
      * destruct (op_eq_dec u u0); try (solve [right; inversion 1; contradiction]).
        destruct (arg_eq_dec l l0); [left; congruence | right; inversion 1 ..].
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
    - destruct (align_eq_dec m1 m2);
        destruct (nat_eq_dec b b0);
        destruct (endian_eq_dec e e0);
        destruct (ty_eq_dec ty ty0);
        try (solve [right; inversion 1; contradiction]); subst.
      destruct (v_eq_dec x x0); [ subst | right; inversion 1];
        destruct (exists_eq_dec _ nat_eq_dec _ (fun n => lt_eq_dec n b0) i i0);
        destruct (v_eq_dec v0 v1); [left; congruence | subst; try (right; inversion 1) ..].
      * pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1); contradiction.
      * pose (inj_pair2_eq_dec _ nat_eq_dec _ _ _ _ H1).
        pose (inj_pair2_eq_dec _ endian_eq_dec _ _ _ _ e).
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ e1).
        pose (inj_pair2_eq_dec _ (@v_eq_dec _ (array m2 b0 e0 ty0)) _ _ _ _ e2); contradiction.
      * pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
      * pose (inj_pair2_eq_dec _ nat_eq_dec _ _ _ _ H1).
        pose (inj_pair2_eq_dec _ endian_eq_dec _ _ _ _ e).
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ e1); contradiction.
      * pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
      * pose (inj_pair2_eq_dec _ nat_eq_dec _ _ _ _ H1).
        pose (inj_pair2_eq_dec _ endian_eq_dec _ _ _ _ e).
        pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ e1); contradiction.
      * pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
    - destruct (kind_eq_dec d1 d2); [ subst | right; inversion 1; contradiction].
      destruct (ty_eq_dec ty ty0); [ subst | right; inversion 1; contradiction].
      destruct (v_eq_dec v0 v1); [left; congruence | right; inversion 1].
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1); contradiction.
  Defined.

End LanguageDecs.
