Require Import NArith.
Require Import Verse.Modular.Equation.
Require Import SetoidClass.
Inductive Zmod (M : positive) :=
| of_N : N -> Zmod M.

Arguments of_N {M}.

Definition to_N {M}(z : Zmod M) :=
  match z with
  | of_N x => x mod (Npos M)
  end%N.

Definition eqZmod {M} : relation (Zmod M) := fun x y => to_N x ≡ to_N y [mod Npos M].

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

Definition add {M} (x y : Zmod M) : Zmod M := of_N (addMod (Npos M) (to_N x) (to_N y)).
Definition mul {M} (x y : Zmod M) : Zmod M := of_N (mulMod (Npos M) (to_N x) (to_N y)).
Definition minus {M} (x y : Zmod M) : Zmod M := of_N( minusMod (Npos M) (to_N x) (to_N y)).
Definition opp {M} (x : Zmod M) : Zmod M := of_N (oppMod (Npos M) (to_N x)).

Require Import setoid_ring.Algebra_syntax.
#[export] Instance zero_Zmod M : Zero (Zmod M) := of_N 0.
#[export] Instance one_Zmod M  : One (Zmod M)  := of_N 1.
#[export] Instance add_Zmod M  : Addition (Zmod M) := add.
#[export] Instance mul_Zmod M  : Multiplication  := @mul M.
#[export] Instance sub_Zmod M  : Subtraction (Zmod M) := minus.
#[export] Instance opp_Zmod M  : Opposite (Zmod M)   := opp.
#[export] Instance setoid_Zmod M : Setoid (Zmod M)   := {| equiv := @eqZmod M; |}.
