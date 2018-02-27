Require Import Verse.Word.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Syntax.
Require Import Verse.Language.

Require Import Bool.
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

Lemma bytes_eq_dec : forall (n : nat), eq_dec (bytes n).
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
  simpl; try apply vec_eq_dec; try apply bytes_eq_dec; trivial.
Qed.

Lemma op_eq_dec {a} : eq_dec (op a).
  unfold eq_dec; unfold decidable.
  destruct a; dependent destruction t1; dependent destruction t2;
    solve [left; congruence |
           right; congruence |
           destruct (nat_eq_dec n n0); solve [left; congruence | right; congruence]
          ].
Qed.
