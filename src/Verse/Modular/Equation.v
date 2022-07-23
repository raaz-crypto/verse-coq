(* begin hide *)
Require Import ZArith.
Require Import NArith.
Require  List.
Require Import Setoid.
Require Export Relation_Definitions.
Import List.ListNotations.


Create HintDb modular.

Hint Resolve
  N.lt_le_incl
  N.mod_lt
  N.mod_le
  : modular.

Hint Rewrite
  N.mod_0_l
  N.mod_same N.add_0_l
  N.add_0_r
  N.mul_1_l
  N.mul_1_r
  N.mod_mod
  N.sub_diag
  : modular.

Lemma npos_neq_0 : forall p : positive, Npos p <> 0%N.
Proof.
  intros p H.
  inversion H.
Qed.

Hint Resolve npos_neq_0 : modular.
(* end hide *)

(** * Simple modular arithmetic proofs.

This module implements a reflection based proving for identities of
the kind X ≡ Y mod M.

 *)

Definition eqMod M  : relation N := fun X Y => (X mod M = Y mod M)%N.
Definition redMod M : relation N := fun X Y => (X = Y mod  M)%N.



#[export] Instance redSubEqMod M (pf : M <> 0%N): subrelation (redMod M) (eqMod M).
intros x y.
intro Hxy.
rewrite Hxy.
apply N.mod_mod; eauto with modular.
Qed.


Notation "X ≡ Y [mod M ]"  := (eqMod M X Y) (at level 70, format "X  ≡  Y  [mod  M ]").
Notation "X <==[mod M ] Y"  := (redMod M X Y) (at level 70, format "X  <==[mod M ]  Y").

Lemma red_eq_mod : forall M x y z,  y ≡ z [mod M] -> x <==[mod M] y  -> x <==[mod M] z.
  intros M x y z.
  intros HyEz.
  unfold redMod.
  rewrite HyEz; trivial.
Qed.



Lemma mod_eqMod : forall M x y, x ≡ y [mod M] -> (x mod  M = y mod M)%N.
  trivial.
Qed.

Lemma eqMod_refl : forall M x, x ≡ x [mod M].
  intros.
  unfold eqMod; trivial.
Qed.

Ltac modring := match goal with
                | [ |- ?X ≡ ?Y [mod ?M] ] =>
                    apply (f_equal (fun y => N.modulo y _)); ring; eauto with modular
                end.

(*

- Rewriting using equations of the kind A ≡ B [mod M]. We give a tactic
  to rewrite with equations of the kind A ≡ B [mod M].

 *)


Tactic Notation "modrewrite" constr(H) := unfold eqMod; rewrite H; try (apply mod_eqMod); eauto with modular.
Tactic Notation "modrewrite" "<-" constr(H) := unfold eqMod; rewrite <- H; try (apply mod_eqMod); eauto with modular.


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


Lemma redMod_trans M (pf : M <> 0%N) : transitive N (redMod M).
Proof.
  intros x y z;
  unfold redMod;
  intros Hxy Hyz;
  rewrite Hxy;
  rewrite Hyz;
  modrewrite N.mod_mod; reflexivity.
Qed.

Definition modMod M (x : N)    : N  := (x mod  M)%N.
Definition addMod M (x y : N)  : N  := modMod M (x + y)%N.
Definition mulMod M (x y : N)  : N  := modMod M (x * y) %N.
Definition oppMod M (x : N)    : N  := (M - modMod M x)%N.
Definition minusMod M (x y : N) : N := addMod M x (oppMod M y).

Ltac simplify := repeat match goal with
                   | [H : ?P |- ?P ] => exact H
                                            (*
                   | [ |- N -> _ ] => let n := fresh "n" in (intro n; simpl)
                   | [ |- _ -> _ ] => intro
                   | [ |- (_ ≡ _ [mod _ ]) -> _ ] => let H := fresh "H" in intro H
                                             *)
                   | [ H : _ ≡ _ [mod _ ]  |- _ ] => rewrite H
                   | [ |- _ <> 0%N ] => eauto with modular
                   | _ => try (repeat autorewrite with modular)
                   end.
Ltac local_crush := simplify; try reflexivity; try eauto with modular.
Ltac simplify_rewrite H := simplify; rewrite H; simplify; rewrite <- H; simplify; reflexivity.
Add Parametric Relation M (pf : M <> 0%N) : N (redMod M)
    transitivity proved by (redMod_trans M pf) as redMod_rel.


Add Parametric Relation M : N (eqMod M)
    reflexivity proved by (eqMod_refl M)
    symmetry proved by  (eqMod_sym M)
    transitivity proved by (eqMod_trans M) as eqMod_rel.

Add Parametric Morphism M  : (modMod M)
    with signature (eqMod M) ==> eq as modMod_mor.
  unfold modMod.
  intros.
  simplify.
Qed.

Add Parametric Morphism M (pf : M <> 0%N) : N.add
    with signature (eqMod M) ==> eqMod M ==> eqMod M as add_mor.
  intros.
  unfold eqMod.
  simplify_rewrite N.add_mod.
Qed.

Add Parametric Morphism M (pf : M <> 0%N): N.mul
    with signature (eqMod M) ==> eqMod M ==> eqMod M as mul_mor.
  intros.
  unfold eqMod.
  simplify_rewrite N.mul_mod.
Qed.

Add Parametric Morphism M (pf : M <> 0%N) : (addMod M)
    with signature (eqMod M) ==> eqMod M ==> eq as addMod_mor.
  intros.
  apply modMod_mor.
  apply add_mor;
    simplify.
Qed.

Add Parametric Morphism M (pf : M <> 0%N) : (mulMod M)
    with signature (eqMod M) ==> eqMod M ==> eq as mulMod_mor.
  intros.
  apply modMod_mor;
    apply mul_mor; simplify.
Qed.

Add Parametric Morphism M : (oppMod M)
    with signature (eqMod M) ==> eq as opMod_mor.
  unfold oppMod.
  intros.
    simplify; reflexivity.
Qed.

Add Parametric Morphism M  (pf : M <> 0%N): (minusMod M)
    with signature eqMod M ==> eqMod M ==> eq  as minusMod_mor.
  intros.
  apply addMod_mor;
    local_crush.
Qed.



Lemma modMod_idemp : forall M, M <> 0%N -> forall x, modMod M x ≡ x [mod M].
  unfold modMod.
  unfold eqMod.
  intros.
  local_crush.
Qed.
Hint Rewrite modMod_idemp : modular.

Lemma modMod_le_M : forall M, M <> 0%N -> forall x, (modMod M x <=  M)%N.
  unfold modMod.
  intros;
  simplify;
  apply N.lt_le_incl.
  apply N.mod_lt; assumption.
Qed.

Hint Resolve modMod_le_M : modular.
Lemma modMod_le : forall M, M<> 0%N -> forall x, (modMod M x <= x)%N.
  unfold modMod.
  simplify; eauto with modular.
Qed.


Lemma zero_mod : forall M, M<>0%N -> M ≡ 0%N [mod M].
  unfold eqMod.
  intros; local_crush.
Qed.

Hint Rewrite zero_mod : modular.

Lemma mul_M_zero : forall M, M <> 0%N -> forall x, M * x ≡ 0 [mod M]%N.
  unfold eqMod.
  intros.
  local_crush.
  rewrite N.mul_mod; local_crush.
Qed.

Hint Rewrite mul_M_zero : modular.

Lemma modMod_0 : forall M, (M <> 0%N) -> forall x, (x - modMod M x ≡ 0 [mod M])%N.
  intros M H x.
  unfold modMod.
  modrewrite (N.div_mod x M).
  modrewrite N.add_mod.
  autorewrite with modular; eauto with modular.
  modrewrite N.add_sub; local_crush.
Qed.

Lemma mod_eq_inv : forall a b, (b <> 0 -> a - b * (a / b) = a mod b)%N.
  intros.
  rewrite (N.mod_eq); eauto.
Qed.
