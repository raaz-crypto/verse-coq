(* begin hide *)
Require Import ZArith.
Require Import NArith.
Require  List.
Require Import Setoid.
Require Export Relation_Definitions.
Import List.ListNotations.


Create HintDb modular.

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

Definition eqMod (M : positive) : relation N  := fun X Y => (X mod (Npos M) = Y mod (Npos M))%N.
Definition redMod (M : positive) : relation N := fun X Y => (X = Y mod (Npos M))%N.



#[export] Instance redSubEqMod M : subrelation (redMod M) (eqMod M).
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



Lemma mod_eqMod : forall M x y, x ≡ y [mod M] -> (x mod (Npos M) = y mod (Npos M))%N.
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


Lemma redMod_trans M : transitive N (redMod M).
Proof.
  intros x y z;
  unfold redMod;
  intros Hxy Hyz;
  rewrite Hxy;
  rewrite Hyz;
  modrewrite N.mod_mod; reflexivity.
Qed.

Definition modMod M (x : N)    : N  := (x mod (Npos M))%N.
Definition addMod M (x y : N)  : N  := modMod M (x + y)%N.
Definition mulMod M (x y : N)  : N  := modMod M (x * y) %N.
Definition oppMod M (x : N)    : N  := (Npos M - modMod M x)%N.
Definition minusMod M (x y : N) : N := addMod M x (oppMod M y)%N.


Add Parametric Relation M : N (redMod M)
    transitivity proved by (redMod_trans M) as redMod_rel.


Add Parametric Relation M : N (eqMod M)
    reflexivity proved by (eqMod_refl M)
    symmetry proved by  (eqMod_sym M)
    transitivity proved by (eqMod_trans M) as eqMod_rel.

Add Parametric Morphism M  : (modMod M)
    with signature (eqMod M) ==> (eqMod M) as modMod_mor.
  intros x y H.
  unfold modMod.
  rewrite H. reflexivity.
Qed.

Add Parametric Morphism M  : N.add
    with signature (eqMod M) ==> eqMod M ==> eqMod M as add_mor.
  intros x1 x2 Hx y1 y2 Hy.
  unfold eqMod.
  modrewrite N.add_mod.
  rewrite Hx. rewrite Hy. modrewrite <- N.add_mod; reflexivity.
Qed.

Add Parametric Morphism M : N.mul
    with signature (eqMod M) ==> eqMod M ==> eqMod M as mul_mor.
  intros x1 x2 Hx y1 y2 Hy.
  unfold eqMod.
  modrewrite N.mul_mod;
  modrewrite Hx.
  modrewrite Hy.
  modrewrite <- N.mul_mod.
  reflexivity.
Qed.


Add Parametric Morphism M  : (addMod M)
    with signature (eqMod M) ==> eqMod M ==> eqMod M as addMod_mor.
  intros x1 x2 Hx y1 y2 Hy.
  unfold addMod.
  rewrite Hx; rewrite Hy; reflexivity.
Qed.




Add Parametric Morphism M  : (mulMod M)
    with signature (eqMod M) ==> eqMod M ==> eqMod M as mulMod_mor.
  intros x1 x2 Hx y1 y2 Hy.
  unfold mulMod;
  rewrite Hx; rewrite Hy; reflexivity.
Qed.

Add Parametric Morphism M : (oppMod M)
    with signature (eqMod M) ==> eqMod M as opMod_mor.
  intros x y H.
  unfold oppMod.
  unfold modMod.
  rewrite H. reflexivity.
Qed.

Add Parametric Morphism M  : (minusMod M)
    with signature eqMod M ==> eqMod M ==> eqMod M as minusMod_mor.
  unfold minusMod.
  intros x1 x2 Hx y1 y2 Hy.
  rewrite Hx.
  rewrite Hy; reflexivity.
Qed.


Lemma modMod_idemp : forall M x, modMod M x ≡ x [mod M].
  intros M x.
  unfold modMod.
  unfold eqMod.
  rewrite N.mod_mod; eauto with modular.
Qed.
Lemma modMod_le_M : forall M x, (modMod M x <= Npos M)%N.
  intros.
  unfold modMod.
  apply N.lt_le_incl.
  apply N.mod_lt. eauto with modular.
Qed.
Lemma modMod_le : forall M x, (modMod M x <= x)%N.
  intros.
  unfold modMod.
  apply N.mod_le; eauto with modular.
Qed.
Lemma zero_mod : forall M, Npos M ≡ 0%N [mod M].
  intros.
  unfold eqMod.
  rewrite N.mod_0_l; eauto with modular.
  rewrite N.mod_same; eauto with modular.
Qed.

Lemma mul_M_zero : forall M x, Npos M * x ≡ 0 [mod M]%N.
  intros.
  unfold eqMod.
  rewrite N.mul_mod; eauto with modular.
  rewrite N.mod_same; eauto with modular.
Qed.


Lemma modMod_0 : forall M x, (x - modMod M x ≡ 0 [mod M])%N.
  intros M x.
  unfold modMod.
  modrewrite (N.div_mod x (Npos M)).
  modrewrite N.add_mod.
  rewrite mul_M_zero.
  modrewrite <- N.add_mod.
  modrewrite N.add_0_l.
  modrewrite N.mod_mod.
  modrewrite N.add_sub.
  rewrite mul_M_zero.
  reflexivity.
Qed.

Lemma mod_eq_inv : forall a b, (b <> 0 -> a - b * (a / b) = a mod b)%N.
  intros.
  rewrite (N.mod_eq); eauto.
Qed.
