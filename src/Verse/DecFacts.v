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

(** Porting over Coq.decidable for decidability with Type *)

Definition decidable (P:Prop) := {P} + {~ P}.

Definition eq_dec (T : Type) := forall (t1 t2 : T),  decidable (t1 = t2).

Definition nat_eq_dec := NPeano.Nat.eq_dec.

Theorem dec_not_not : forall P:Prop, decidable P -> (~ P -> False) -> P.
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_True : decidable True.
Proof.
unfold decidable; auto.
Qed.

Theorem dec_False : decidable False.
Proof.
unfold decidable, not; auto.
Qed.

Theorem dec_or :
 forall A B:Prop, decidable A -> decidable B -> decidable (A \/ B).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_and :
 forall A B:Prop, decidable A -> decidable B -> decidable (A /\ B).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_not : forall A:Prop, decidable A -> decidable (~ A).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_imp :
 forall A B:Prop, decidable A -> decidable B -> decidable (A -> B).
Proof.
unfold decidable; tauto.
Qed.

Theorem dec_iff :
 forall A B:Prop, decidable A -> decidable B -> decidable (A<->B).
Proof.
unfold decidable. tauto.
Qed.

Theorem not_not : forall P:Prop, decidable P -> ~ ~ P -> P.
Proof.
unfold decidable; tauto.
Qed.

Theorem not_or : forall A B:Prop, ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
tauto.
Qed.

Theorem not_and : forall A B:Prop, decidable A -> ~ (A /\ B) -> ~ A \/ ~ B.
Proof.
unfold decidable; tauto.
Qed.

Theorem not_imp : forall A B:Prop, decidable A -> ~ (A -> B) -> A /\ ~ B.
Proof.
unfold decidable; tauto.
Qed.

Theorem imp_simp : forall A B:Prop, decidable A -> (A -> B) -> ~ A \/ B.
Proof.
unfold decidable; tauto.
Qed.

Theorem not_iff :
  forall A B:Prop, decidable A -> decidable B ->
    ~ (A <-> B) -> (A /\ ~ B) \/ (~ A /\ B).
Proof.
unfold decidable; tauto.
Qed.

(** Results formulated with iff, used in FSetDecide.
    Negation are expanded since it is unclear whether setoid rewrite
    will always perform conversion. *)

(** We begin with lemmas that, when read from left to right,
    can be understood as ways to eliminate uses of [not]. *)

Theorem not_true_iff : (True -> False) <-> False.
Proof.
tauto.
Qed.

Theorem not_false_iff : (False -> False) <-> True.
Proof.
tauto.
Qed.

Theorem not_not_iff : forall A:Prop, decidable A ->
  (((A -> False) -> False) <-> A).
Proof.
unfold decidable; tauto.
Qed.

Theorem contrapositive : forall A B:Prop, decidable A ->
  (((A -> False) -> (B -> False)) <-> (B -> A)).
Proof.
unfold decidable; tauto.
Qed.

Lemma or_not_l_iff_1 : forall A B: Prop, decidable A ->
  ((A -> False) \/ B <-> (A -> B)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_l_iff_2 : forall A B: Prop, decidable B ->
  ((A -> False) \/ B <-> (A -> B)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_1 : forall A B: Prop, decidable A ->
  (A \/ (B -> False) <-> (B -> A)).
Proof.
unfold decidable. tauto.
Qed.

Lemma or_not_r_iff_2 : forall A B: Prop, decidable B ->
  (A \/ (B -> False) <-> (B -> A)).
Proof.
unfold decidable. tauto.
Qed.

Lemma imp_not_l : forall A B: Prop, decidable A ->
  (((A -> False) -> B) <-> (A \/ B)).
Proof.
unfold decidable. tauto.
Qed.


(** Moving Negations Around:
    We have four lemmas that, when read from left to right,
    describe how to push negations toward the leaves of a
    proposition and, when read from right to left, describe
    how to pull negations toward the top of a proposition. *)

Theorem not_or_iff : forall A B:Prop,
  (A \/ B -> False) <-> (A -> False) /\ (B -> False).
Proof.
tauto.
Qed.

Lemma not_and_iff : forall A B:Prop,
  (A /\ B -> False) <-> (A -> B -> False).
Proof.
tauto.
Qed.

Lemma not_imp_iff : forall A B:Prop, decidable A ->
  (((A -> B) -> False) <-> A /\ (B -> False)).
Proof.
unfold decidable. tauto.
Qed.

Lemma not_imp_rev_iff : forall A B : Prop, decidable A ->
  (((A -> B) -> False) <-> (B -> False) /\ A).
Proof.
unfold decidable. tauto.
Qed.

(** With the following hint database, we can leverage [auto] to check
    decidability of propositions. *)

Hint Resolve dec_True dec_False dec_or dec_and dec_imp dec_not dec_iff
 : decidable_prop.

(** [solve_decidable using lib] will solve goals about the
    decidability of a proposition, assisted by an auxiliary
    database of lemmas.  The database is intended to contain
    lemmas stating the decidability of base propositions,
    (e.g., the decidability of equality on a particular
    inductive type). *)

Tactic Notation "solve_decidable" "using" ident(db) :=
  match goal with
   | |- decidable _ =>
     solve [ auto 100 with decidable_prop db ]
  end.

Tactic Notation "solve_decidable" :=
  solve_decidable using core.


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

Lemma endian_eq_dec : forall (e1 e2 : endian), {e1 = e2} + {e1 <> e2}.
  decide equality.
Qed.

Lemma ty_eq_dec : forall {k} (t1 t2 : type k), {t1 = t2} + {t1 <> t2}.
  destruct k.

  abstract (dependent destruction t1; dependent destruction t2; [try (right; congruence) ..];
            [destruct (nat_eq_dec n n0); [left | right ..]; try congruence |
             destruct (nat_eq_dec n n1), (nat_eq_dec n0 n2); [left | right .. ]; try congruence])
  using directTy_eq_dec.

  dependent destruction t1; dependent destruction t2.
  destruct (nat_eq_dec n n0); destruct (endian_eq_dec e e0); destruct (directTy_eq_dec t1 t2);
    first [ left; congruence | right; congruence ].
Qed.

Lemma bytes_dec : forall (n : nat) (a b : bytes n), {a = b} + {a <> b}.
  unfold bytes. destruct a. destruct b0.
  unfold Bvector.Bvector in b, b0.
  pose (vec_eq_dec bool bool_dec (8 * n) b b0) as s.
  destruct s.
  left; apply f_equal; trivial.
  right; unfold not; inversion 1; contradiction.
Qed.

Lemma constant_dec {k} (ty : type k) : forall (a b : constant ty), {a = b} + {a <> b}.
  induction ty;
  simpl; try apply vec_eq_dec; try apply bytes_dec; trivial.
Qed.

Section LanguageDecs.

  Variable v : VariableT.
  Variable v_eq_dec : forall {k} {ty : type k} (v1 v2 : v _ ty), {v1 = v2} + {v1 <> v2}.

  Arguments v_eq_dec [k ty] _.

  Lemma op_eq_dec {a} (o1 o2 : op a) : {o1 = o2} + {o1 <> o2}.
    destruct a; dependent destruction o1; dependent destruction o2;
      solve [left; congruence |
             right; congruence |
             destruct (nat_eq_dec n n0); solve [left; congruence | right; congruence]
            ].
  Qed.


  (*
  Lemma arg_eq_dec : forall (a1 a2 : {ty : type direct & arg _ ty}), {a1 = a2} + {a1 <> a2}.
    destruct a1, a2.
    dependent destruction a; dependent destruction a0;
      try (solve [(right; unfold not; inversion 1)]).
    * destruct (ty_eq_dec x x0); subst; [ | right ; unfold not; inversion 1; contradiction ..].
      destruct (v_eq_dec v0 v1); [left; congruence | right];
        unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1); contradiction.
    * destruct (ty_eq_dec x x0); subst; [ | right ; unfold not; inversion 1; contradiction ..].
      destruct (constant_dec x0 c c0); [left; congruence | right];
        unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1).
      contradiction.
    * destruct (ty_eq_dec x x0); destruct (eq_dec b b0);
        destruct (endian_eq_dec e e0); destruct (ty_eq_dec x x0);
          subst; [ | right; unfold not; inversion 1; contradiction ..].
      destruct (v_eq_dec v0 v1).
      destruct (exists_eq_dec _ eq_dec _ (fun n => lt_eq_dec n b0) s s0);
        [ left; congruence | right ].
      unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ eq_dec _ _ _ _ H2); contradiction.
      right; unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ eq_dec _ _ _ _ H1).
      pose (inj_pair2_eq_dec _ endian_eq_dec _ _ _ _ e).
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ e1); contradiction.
  Defined.
   *)

  Lemma arg_eq_dec {ty : type direct} : forall (a1 a2 : arg v _ ty), {a1 = a2} + {a1 <> a2}.
    dependent destruction a1; dependent destruction a2;
      try (solve [(right; unfold not; inversion 1)]).
    * destruct (v_eq_dec v0 v1); [left; congruence | right];
        unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1); contradiction.
    * destruct (constant_dec ty c c0); [left; congruence | right];
        unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H1).
      contradiction.
    * destruct (nat_eq_dec b b0);
        destruct (endian_eq_dec e e0);
        subst; [ | right; unfold not; inversion 1; contradiction ..].
      destruct (v_eq_dec v0 v1).
      destruct (exists_eq_dec _ nat_eq_dec _ (fun n => lt_eq_dec n b0) s s0);
        [ left; congruence | right ].
      unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ nat_eq_dec _ _ _ _ H2); contradiction.
      right; unfold not; inversion 1.
      pose (inj_pair2_eq_dec _ nat_eq_dec _ _ _ _ H1).
      pose (inj_pair2_eq_dec _ endian_eq_dec _ _ _ _ e).
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ e1); contradiction.
  Defined.

  Definition instruction_eq_dec (i1 i2 : instruction v) : {i1 = i2} + {i1 <> i2}.
    destruct i1 as [a1]; destruct i2 as [a2].
    dependent destruction a1; dependent destruction a2; try (solve [right; inversion 1]);
      destruct (ty_eq_dec ty ty0); try (solve [right; inversion 1; contradiction]); subst.
    - destruct (op_eq_dec b b0); try (solve [right; inversion 1; contradiction]).
      destruct (arg_eq_dec a a2); destruct (arg_eq_dec a0 a3); destruct (arg_eq_dec a1 a4);
        [left; congruence | right; inversion 1 ..].
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H4); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H4); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H4); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
    - destruct (op_eq_dec u u0); try (solve [right; inversion 1; contradiction]).
      destruct (arg_eq_dec a a1); destruct (arg_eq_dec a0 a2);
        [left; congruence | right; inversion 1 ..].
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
    - destruct (op_eq_dec b b0); try (solve [right; inversion 1; contradiction]).
      destruct (arg_eq_dec a a1); destruct (arg_eq_dec a0 a2);
        [left; congruence | right; inversion 1 ..].
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H3); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
    - destruct (op_eq_dec u u0); try (solve [right; inversion 1; contradiction]).
      destruct (arg_eq_dec a a0); [left; congruence | right; inversion 1 ..].
      pose (inj_pair2_eq_dec _ ty_eq_dec _ _ _ _ H2); contradiction.
  Defined.

End LanguageDecs.
