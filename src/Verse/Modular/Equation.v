(* begin hide *)
Require Import ZArith.
Require Import NArith.
Require  List.
Require Import Setoid.
Require Export Relation_Definitions.
Import List.ListNotations.


Create HintDb localdb.
Local Declare Scope exp_scope.
Local Delimit Scope exp_scope with exp.

(* end hide *)

(** * Simple modular arithmetic proofs.

This module implements a reflection based proving for identities of
the kind X ≡ Y mod M.

 *)

Definition eqMod (M : N) : relation N := fun X Y => (X mod M = Y mod M)%N.
Notation "X ≡ Y [mod M ]"  := (eqMod M X Y) (at level 70, format "X  ≡  Y  [mod  M ]").


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


Tactic Notation "modrewrite" constr(H) := unfold eqMod; rewrite H; try (apply mod_eqMod); trivial.
Tactic Notation "modrewrite" "<-" constr(H) := unfold eqMod; rewrite <- H; try (apply mod_eqMod); trivial.


Ltac automodrewrite := repeat match goal with
                         | [ H : _ ≡ _ [mod ?M] |- _ ] => modrewrite H
                         end.

Lemma eqMod_sym : forall M x y, x ≡ y [mod M] -> y ≡ x [mod M].
  intros M x y hxEqy;
  automodrewrite; apply eqMod_refl.
Qed.

Lemma eqMod_trans : forall M x y z, x ≡ y [mod M] -> y ≡ z [mod M] -> x ≡ z [mod M].
  intros x y z M hxEqy.
  automodrewrite; apply eqMod_refl.
Qed.

Definition addMod (M x y : N)   := ((x + y) mod M)%N.
Definition mulMod (M x y : N)   := ((x * y) mod M)%N.
Definition oppMod (M x : N)     := (M - (x mod M))%N.
Definition minusMod M (x y : N) := addMod M x (oppMod M y)%N.

Add Parametric Relation M : N (eqMod M)
    reflexivity proved by (eqMod_refl M)
    symmetry proved by  (eqMod_sym M)
    transitivity proved by (eqMod_trans M) as eqMod_rel.

Add Parametric Morphism M (pf : M <> 0%N) : N.add
    with signature (eqMod M) ==> eqMod M ==> eqMod M as add_mor.
  intros x1 x2 Hx y1 y2 Hy.
  modrewrite N.add_mod.
  rewrite Hx. rewrite Hy. modrewrite <- N.add_mod.
  reflexivity.
Qed.

Add Parametric Morphism M  (pf : M <> 0%N) : N.mul
    with signature (eqMod M) ==> eqMod M ==> eqMod M as mul_mor.
  intros x1 x2 Hx y1 y2 Hy.
  modrewrite N.mul_mod.
  modrewrite Hx.
  rewrite Hy.
  modrewrite <- N.mul_mod.
  reflexivity.
Qed.



Add Parametric Morphism M  (pf : M <> 0%N) : (mulMod M)
    with signature (eqMod M) ==> eqMod M ==> eqMod M as mulMod_mor.
  intros x1 x2 Hx y1 y2 Hy.
  unfold mulMod.
  modrewrite N.mul_mod.
  fold mulMod;
    rewrite Hx.
  rewrite Hy.
  modrewrite <- N.mul_mod.
  reflexivity.
Qed.

Add Parametric Morphism M  (pf : M <> 0%N) : (oppMod M)
    with signature (eqMod M) ==> eqMod M as opMod_mor.
  intros x y H.
  unfold oppMod.
  rewrite H. reflexivity.
Qed.

Add Parametric Morphism M  (pf : M <> 0%N) : (minusMod M)
    with signature eqMod M ==> eqMod M ==> eqMod M as minusMod_mor.
  unfold minusMod.
  intros x1 x2 Hx y1 y2 Hy.
  unfold oppMod.
  unfold addMod.

  rewrite N.add_mod; trivial.
  rewrite Hx; trivial.
  rewrite Hy; trivial. modrewrite <- N.add_mod;  reflexivity.
Qed.
