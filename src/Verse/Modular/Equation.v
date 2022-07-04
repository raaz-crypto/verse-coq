(* begin hide *)
Require Import ZArith.
Require Import NArith.
Require  List.
Import List.ListNotations.


Create HintDb localdb.
Local Declare Scope exp_scope.
Local Delimit Scope exp_scope with exp.

(* end hide *)

(** * Simple modular arithmetic proofs.

This module implements a reflection based proving for identities of
the kind X ≡ Y mod M.

 *)

Definition eqMod (M X Y : N) : Prop := (X mod M = Y mod M)%N.
Notation "X ≡ Y [mod M ]"  := (eqMod M X Y) (at level 70).


Lemma mod_eqMod : forall M x y, x ≡ y [mod M] -> (x mod M = y mod M)%N.
  trivial.
Qed.

Lemma eqMod_refl : forall M x, x ≡ x [mod M].
  intros.
  unfold eqMod; trivial.
Qed.

Ltac modring M := match goal with
                  | [ |- ?X ≡ ?Y [mod ?M] ] =>
                      apply (f_equal (fun y => N.modulo y M)); ring
                  end.

(*

- Rewriting using equations of the kind A ≡ B [mod M]. We give a tactic
  to rewrite with equations of the kind A ≡ B [mod M].

 *)

Tactic Notation "modrewrite" constr(H) := unfold eqMod; rewrite H; apply mod_eqMod.
Tactic Notation "modrewrite" "<-" constr(H) := unfold eqMod; rewrite <- H; apply mod_eqMod.


Ltac automodrewrite := repeat match goal with
                         | [ H : _ ≡ _ [mod ?M] |- _ ] => modrewrite H
                         end.

Lemma eqMod_sym : forall M x y, x ≡ y [mod M] -> y ≡ x [mod M].
  intros x y M hxEqy.
  automodrewrite; apply eqMod_refl.
Qed.

Lemma eqMod_trans : forall M x y z, x ≡ y [mod M] -> y ≡ z [mod M] -> x ≡ z [mod M].
  intros x y z M hxEqy.
  automodrewrite; apply eqMod_refl.
Qed.


Add Parametric Relation M : N (@eqMod M)
    reflexivity proved by (eqMod_refl M)
    symmetry proved by  (eqMod_sym M)
    transitivity proved by (eqMod_trans M) as eqmod_rel.
