Require Import NArith.
Require Import Verse.Modular.Equation.
Require Import Setoid.
Require Import SetoidClass.
Require Import RelationClasses.
Require Export Relation_Definitions.
Create HintDb localdb.

Inductive Zmod (M : positive) :=
| of_N : N -> Zmod M.

Arguments of_N {M}.

Definition to_N {M}(z : Zmod M) :=
  match z with
  | of_N x => modMod M x
  end%N.

Add Parametric Morphism M : (@to_N M) with signature
    eq ==> eqMod M as to_N_morph.
  intro y. reflexivity.
Qed.

Definition eqZmod {M} : relation (Zmod M) := fun x y => to_N x ≡ to_N y [mod M].

Lemma eqZmod_refl M : reflexive (Zmod M) eqZmod.
  intros x;
  reflexivity.
Qed.

Lemma eqZmod_sym M : symmetric (Zmod M) eqZmod.
  intros x y;
    symmetry; trivial.
Qed.

Lemma eqZmod_trans M : transitive (Zmod M) eqZmod.
  intros x y z; unfold eqZmod.
    transitivity (to_N y); trivial.
Qed.



Add Parametric Relation M : (Zmod M) eqZmod
    reflexivity proved by (eqZmod_refl M)
    symmetry proved by (eqZmod_sym M)
    transitivity proved by (eqZmod_trans M) as zmod_rel.

Definition add {M} (x y : Zmod M) : Zmod M := of_N (addMod M (to_N x) (to_N y)).
Definition mul {M} (x y : Zmod M) : Zmod M := of_N (mulMod M (to_N x) (to_N y)).
Definition minus {M} (x y : Zmod M) : Zmod M := of_N (minusMod M (to_N x) (to_N y)).
Definition opp {M} (x : Zmod M) : Zmod M := of_N (oppMod M (to_N x)).

#[local] Hint Unfold eqZmod add mul minus opp
  : localdb.

#[local] Ltac prepare_goals := repeat ( autounfold with localdb;
                                        match goal with
                                        | [ |- Zmod _ -> _ ] => let x := fresh "x" in (intro x; simpl)
                                        | [ |- _ -> _ ] => let H := fresh "H" in intro H
                                        | [ H : _ ≡ _ [mod _ ]  |- _ ] => rewrite H
                                        | _ => repeat (rewrite modMod_idemp); idtac
                                        end).
#[local] Ltac crush := prepare_goals; try (simpl; reflexivity); try modring.
#[local] Ltac crush_rewrite H := crush; try (rewrite H); crush.

Require Import setoid_ring.Algebra_syntax.
#[export] Instance zero_Zmod M : Zero (Zmod M) := of_N 0.
#[export] Instance one_Zmod M  : One (Zmod M)  := of_N 1.
#[export] Instance add_Zmod M  : Addition (Zmod M) := add.
#[export] Instance mul_Zmod M  : Multiplication  := @mul M.
#[export] Instance sub_Zmod M  : Subtraction (Zmod M) := minus.
#[export] Instance opp_Zmod M  : Opposite (Zmod M)   := opp.
#[export] Instance setoid_Zmod M : Setoid (Zmod M)   := {| SetoidClass.equiv := @eqZmod M; |}.

Add Parametric Morphism (M : positive) : addition  with signature
    (eqZmod ==> eqZmod ==> @eqZmod M) as add_mor.
Proof.
  crush.
Qed.

Add Parametric Morphism (M : positive) : multiplication  with signature
    (@eqZmod M ==> eqZmod ==> eqZmod) as mul_mor.
Proof.
  crush.
Qed.

Add Parametric Morphism (M : positive) : subtraction  with signature
    (@eqZmod M ==> eqZmod ==> eqZmod) as minus_mor.
Proof.
  crush.
Qed.


Add Parametric Morphism (M : positive) : opposite  with signature
    (@eqZmod M ==> eqZmod) as opp_mor.
Proof.
  crush.
Qed.

Program Definition modular_ring (M : positive)
  : ring_theory
      0
      1
      addition
      multiplication
      subtraction
      opposite
      (@eqZmod M)
  := {|
      Radd_0_l   := _;
      Radd_comm   := _;
      Radd_assoc := _;
      Rmul_1_l   := _;
      Rmul_comm  := _;
      Rmul_assoc := _;
      Rdistr_l   := _;
      Rsub_def   := _;
      Ropp_def   := _
    |}.

#[local] Hint Unfold eqZmod addition multiplication subtraction opposite zero one addMod mulMod oppMod minusMod
  : localdb.

Solve All Obligations with crush.
Next Obligation.
  prepare_goals; simpl.
  repeat rewrite modMod_idemp.
   crush.
Qed.

Next Obligation.
  prepare_goals.
  simpl.
  repeat rewrite modMod_idemp.
  crush.
  rewrite N.add_sub_assoc; try apply modMod_le_M.
  rewrite N.add_sub_swap; try apply (modMod_le M (to_N x)).
  rewrite modMod_0.
  rewrite N.add_0_l.
  rewrite zero_mod; reflexivity.
Qed.
