Require Import NArith.
Require Import Verse.Modular.Equation.

Inductive Zmod (M : positive) :=
| of_N : N -> Zmod M.

Arguments of_N {M}.

Definition to_N {M}(z : Zmod M) :=
  match z with
  | of_N x => x mod (Npos M)
  end%N.

Definition eqZmod {M} (x y : Zmod M) : Prop := to_N x ≡ to_N y [mod Npos M].

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
