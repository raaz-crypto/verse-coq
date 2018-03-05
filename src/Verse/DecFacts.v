Require Import Verse.Word.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Syntax.
Require Import Verse.Language.

Require Import Eqdep_dec.
Require Import Bool.
Require Import Equality.
Require Vector.
Require Import VectorEq.


Notation decidable P := ({P} + {~ P}) (only parsing).

Theorem dec_not_not : forall P:Prop, decidable P -> (~ P -> False) -> P.
Proof.
tauto.
Defined.

Theorem dec_True : decidable True.
Proof.
auto.
Defined.

Theorem dec_False : decidable False.
Proof.
unfold not; auto.
Defined.

Theorem dec_or :
 forall A B:Prop, decidable A -> decidable B -> decidable (A \/ B).
Proof.
tauto.
Defined.

Theorem dec_and :
 forall A B:Prop, decidable A -> decidable B -> decidable (A /\ B).
Proof.
tauto.
Defined.

Theorem dec_not : forall A:Prop, decidable A -> decidable (~ A).
Proof.
tauto.
Defined.

Theorem dec_imp :
 forall A B:Prop, decidable A -> decidable B -> decidable (A -> B).
Proof.
tauto.
Defined.

Theorem dec_iff :
 forall A B:Prop, decidable A -> decidable B -> decidable (A<->B).
Proof.
tauto.
Defined.

Notation eq_dec A := (forall A1 A2 : A, {A1 = A2} + {A1 <> A2}) (only parsing).
Definition nat_eq_dec : eq_dec nat := NPeano.Nat.eq_dec.

Definition bool_eq_dec : eq_dec bool := bool_dec.

Hint Resolve dec_True dec_False dec_or dec_and dec_imp dec_not dec_iff nat_eq_dec bool_eq_dec
 : decidable_prop.

(** [solve_decidable using lib] will solve goals about the
    decidability of a proposition, assisted by an auxiliary
    database of lemmas.  The database is intended to contain
    lemmas stating the decidability of base propositions,
    (e.g., the decidability of equality on a particular
    inductive type). *)

Tactic Notation "solve_decidable" "using" ident(db) :=
  intros;
  match goal with
  | |- decidable _ => solve [ auto 100 with decidable_prop db ]
  end.

Tactic Notation "solve_decidable" := solve_decidable using core.

Ltac undep_eq :=
  match goal with
  | [ H : existT _ _ ?a = existT _ _ ?b |- _ ]
    => let He := fresh H in
       assert (He : a = b) by (refine (inj_pair2_eq_dec _ _ _ _ _ _ H);
                             auto with decidable_prop);
       rewrite He in *; clear H
  end.

Ltac crush_eq_dec := repeat aux_match; aux_solve
  with aux_match :=  (intros;
                     match goal with
                     | [ H1 : ?T, H2 : ?T, _ : _ <> _ |- _ ] => idtac
                     | [ H1 : ?T, H2 : ?T, H3 : ?T |- _ ]    => aux_cases2 H1 H3 T
                     | [ H1 : ?T, H2 : ?T |- _ ]             => aux_cases H1 H2 T
                     end)
  with aux_cases H1 H2 T :=
                       let T_eq_dec := fresh "T" in assert (T_eq_dec : eq_dec T) by solve_decidable;
                                                    destruct (T_eq_dec H1 H2) as [ eq | ];
                                                    [ subst | ..]; clear T_eq_dec
  (* Heuristic for pairing up four hypothesis of the same type by alternation *)
  with aux_cases2 H1 H2 T :=
                       let T_eq_dec := fresh "T" in assert (T_eq_dec : eq_dec T) by solve_decidable;
                                                    destruct (T_eq_dec H1 H2) as [ eq | ];
                                                    [ symmetry in eq; subst | ..]; clear T_eq_dec
  with aux_solve := try solve [left; constructor; trivial |
                               right; inversion 1; repeat undep_eq; try congruence; easy ].

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
    apply (Vector.eq_dec T eqdec_eqb eqdec_eqbeq).
  Defined.

End DecFacts.

(** Decidable equality for Verse constructs *)

Scheme Equality for kind.

Lemma endian_eq_dec : eq_dec endian.
  decide equality.
Defined.

Scheme Equality for align.

Hint Resolve vec_eq_dec kind_eq_dec endian_eq_dec align_eq_dec : decidable_prop.

Lemma ty_eq_dec : forall {k}, eq_dec (type k).
  induction k.
  abstract (dependent destruction A1; dependent destruction A2; crush_eq_dec) using directTy_eq_dec.
  remember directTy_eq_dec.
  dependent destruction A1; dependent destruction A2;
  crush_eq_dec.
Qed.

Lemma bytes_eq_dec : forall (n : nat), eq_dec (bytes n).
  destruct A1. destruct A2.
  unfold Bvector.Bvector in b, b0.
  crush_eq_dec.
Defined.

Hint Resolve ty_eq_dec bytes_eq_dec : decidable_prop.
Lemma constant_eq_dec ty : eq_dec (constant ty).
  dependent destruction ty; unfold constant; simpl; unfold StandardWord.wordDenote;
  crush_eq_dec.
Defined.

Lemma op_eq_dec {la ra} : eq_dec (op la ra).
  destruct la; destruct ra; dependent destruction A1; dependent destruction A2;
    crush_eq_dec.
Defined.

Hint Resolve vec_eq_dec kind_eq_dec endian_eq_dec align_eq_dec ty_eq_dec bytes_eq_dec constant_eq_dec op_eq_dec
  : decidable_prop.
