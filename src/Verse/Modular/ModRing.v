Require Import NArith.
Require Import ZArith.
Require Import Verse.Modular.Equation.
Require Import Setoid.
Require Import SetoidClass.
Require Import RelationClasses.
Require Export Relation_Definitions.
Create HintDb localdb.


Inductive Zmod (M : positive) :=
| of_N : N -> Zmod M.

Arguments of_N {M}.

Declare Scope modular_scope.
Delimit Scope modular_scope with modular.
Bind Scope modular_scope with Zmod.


Definition to_N {M}(z : Zmod M) :=
  match z with
  | of_N x => modMod (Npos M) x
  end%N.


Definition eqZmod {M} : relation (Zmod M) := fun x y => match x, y with
                                                     | of_N x, of_N y => x ≡ y [mod (Npos M)]
                                                     end.
Definition eqZmodb {M}(x y : Zmod M) := to_N x ≡? to_N y [mod (Npos M)].

Lemma eqZmod_spec M : forall (x y : Zmod M), eqZmodb x y = true -> eqZmod x y.
  intros x y.
  destruct x; destruct y.
  unfold eqZmodb.
  unfold eqZmod.
  simpl.
  intro Hyp.
  assert (modMod (N.pos M) n  ≡ modMod (N.pos M) n0 [mod N.pos M]) by (apply eqModb_ok; trivial).
  modrewrite <- modMod_idemp.
  rewrite H.
  modrewrite modMod_idemp.
  reflexivity.
Qed.

Lemma to_vs_of_N_spec M : forall n : N, to_N (@of_N M n) = (n mod (Npos M))%N.
  trivial.
Qed.

Hint Unfold eqZmod : localdb.
#[local] Ltac simplify := repeat (autounfold with localdb; Equation.simplify).
#[local] Ltac zmod_destruct := repeat (match goal with
                                       | [ x : Zmod _  |- _ ] => destruct x; simpl
                                       | [ |- _ -> _ ] => intro
                                       | _ => simplify
                                       end).
#[local] Ltac local_crush := zmod_destruct;  try reflexivity; try eauto with modular; try modring.
Lemma eqZmod_refl M : reflexive (Zmod M) eqZmod.
  unfold reflexive.
  local_crush.
Qed.


Lemma eqZmod_sym M : symmetric (Zmod M) eqZmod.
  unfold symmetric.
  local_crush.
Qed.

Lemma eqZmod_trans M : transitive (Zmod M) eqZmod.
  unfold transitive;
    local_crush.
Qed.


Add Parametric Relation M : (Zmod M) eqZmod
    reflexivity proved by (eqZmod_refl M)
    symmetry proved by (eqZmod_sym M)
    transitivity proved by (eqZmod_trans M) as zmod_rel.

Add Parametric Morphism M : (@of_N M) with signature
    eqMod (Npos M) ==> eqZmod as of_N_morph.
  local_crush.
Qed.

Add Parametric Morphism M : (@to_N M) with signature
    eqZmod ==> eq as to_N_morph.
  local_crush.
Qed.


Definition add {M} (x y : Zmod M) : Zmod M := of_N (to_N x + to_N y).
Definition mul {M} (x y : Zmod M) : Zmod M := of_N (to_N x * to_N y).
Definition opp {M} (x : Zmod M) : Zmod M := match x with
                                            | of_N n => of_N (oppMod (Npos M) n)
                                            end.

Definition minus {M}(x y : Zmod M) : Zmod M :=  add x (opp y).

Definition of_positive [M](p : positive) : Zmod M := of_N (Npos p).
Definition of_negative [M](p : positive) : Zmod M := opp (of_positive p).
Definition of_Zero {M} : Zmod M := of_N 0.
Definition idZ := @id Z.

Number Notation Zmod idZ idZ
                (via Z mapping [ [of_Zero] => Z0 , [of_positive] => Zpos, [of_negative] => Zneg ]) : modular_scope.

#[local] Hint Unfold add mul minus opp
  : localdb.


#[local] Ltac prepare_goals := repeat ( try (autounfold with localdb);
                                        match goal with
                                        | [ |- Zmod _ -> _ ] => let x := fresh "x" in (intro x; simpl)
                                        | [ |- N -> _ ] => let n := fresh "n" in intro n; simpl
                                        | [ |- _ -> _ ] => let H := fresh "H" in intro H
                                        | [ H : _ ≡ _ [mod _ ]  |- _ ] => rewrite H
                                        | _ => repeat (rewrite (modMod_idemp (Npos _) (npos_neq_0 _)) ); eauto with modular
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
#[export] Instance eq_Zmod M   : Equality   := @eqZmod M.
#[export] Instance setoid_Zmod M : Setoid (Zmod M)   := {| SetoidClass.equiv := @eqZmod M; |}.

Hint Unfold addition multiplication subtraction opposite add_Zmod mul_Zmod zero one: localdb.
Add Parametric Morphism (M : positive) : to_N with signature
    @eqZmod M ==> eq as to_N_mor.
Proof.
  local_crush.
Qed.

Add Parametric Morphism (M : positive) : of_N with signature
    @eqMod (Npos M) ==> @eqZmod M as of_N_mor.
Proof.
  local_crush.
Qed.

Add Parametric Morphism (M : positive) : addition  with signature
    (eqZmod ==> eqZmod ==> @eqZmod M) as add_mor.
Proof.
  local_crush.
Qed.

Add Parametric Morphism (M : positive) : multiplication  with signature
    (@eqZmod M ==> eqZmod ==> eqZmod) as mul_mor.
  local_crush.
Qed.

Add Parametric Morphism (M : positive) : subtraction  with signature
    (@eqZmod M ==> eqZmod ==> eqZmod) as minus_mor.
Proof.
  local_crush.
Qed.


Add Parametric Morphism (M : positive) : opposite  with signature
    (@eqZmod M ==> eqZmod) as opp_mor.
Proof.
  local_crush.
Qed.

Lemma Zmod_add_0_l {M} : forall x : Zmod M, (0 + x) == x.
  local_crush.
Qed.


Lemma Zmod_add_comm {M} :  forall x y : Zmod M, (x + y) == (y + x).
  local_crush.
Qed.

Lemma Zmod_add_assoc {M} : forall x y z: Zmod M, (x + (y + z)) == (x + y + z).
  local_crush.
Qed.

Lemma Zmod_mul_1_l {M} : forall x : Zmod M, 1 * x == x.
  local_crush.
Qed.

Lemma Zmod_mul_comm {M} : forall x y : Zmod M, x * y == y * x.
  local_crush; simpl.
Qed.

Lemma Zmod_mul_assoc {M} : forall x y z : Zmod M, x * (y * z) == x * y * z.
  local_crush.
Qed.

Lemma Zmod_distr_l {M} : forall x y a : Zmod M, (x + y) * a == x * a + y * a.
  local_crush.
Qed.


Lemma Zmod_sub_def {M}  : forall x y : Zmod M, (x - y) == x + - y.
  local_crush.
Qed.

Lemma Zmod_opp_def {M} : forall x : Zmod M, x + opposite x == 0.
  intro x.
  apply of_N_mor.
  unfold to_N.
  destruct x.
  unfold opposite.
  unfold opp_Zmod.
  unfold opp.
  unfold oppMod.
  unfold eqMod.
  rewrite N.add_mod; local_crush.
  rewrite N.add_mod_idemp_r; local_crush.
  rewrite N.add_sub_assoc; local_crush.
  rewrite N.add_sub_swap; local_crush.
Qed.


Print semi_ring_theory.
Program Definition modular_semi_ring (M : positive)
  : semi_ring_theory
      0
      1
      addition
      multiplication
      (@eqZmod M) :=
  {|
    SRadd_0_l   := Zmod_add_0_l;
    SRadd_comm  := Zmod_add_comm;
    SRadd_assoc := Zmod_add_assoc;
    SRmul_1_l   := Zmod_mul_1_l;
    SRmul_comm  := Zmod_mul_comm;
    SRmul_assoc := Zmod_mul_assoc;
    SRdistr_l   := Zmod_distr_l
  |}.

Solve All Obligations with reflexivity.


Definition modular_ring (M : positive)
  : ring_theory
      0
      1
      addition
      multiplication
      subtraction
      opposite
      (@eqZmod M)
  := {|
      Radd_0_l   := Zmod_add_0_l;
      Radd_comm  := Zmod_add_comm;
      Radd_assoc := Zmod_add_assoc;
      Rmul_1_l   := Zmod_mul_1_l;
      Rmul_comm  := Zmod_mul_comm;
      Rmul_assoc := Zmod_mul_assoc;
      Rdistr_l   := Zmod_distr_l;
      Rsub_def   := Zmod_sub_def;
      Ropp_def   := Zmod_opp_def
    |}.



Program Definition modular_semi_morph (M : positive)
  : semi_morph
      0
      1
      addition
      multiplication
      (@eqZmod M)
      0%N
      1%N
      N.add
      N.mul
      (@eqModb (Npos M))
      (@of_N M)
  := {|
    Smorph0 := _;
    Smorph1 := _;
    Smorph_add := _;
    Smorph_mul := _;
    Smorph_eq := _
    |}.

Solve Obligations with (try reflexivity).

Next Obligation.
  modrewrite N.add_mod. reflexivity.
Qed.

Next Obligation.
  modrewrite N.mul_mod; reflexivity.
Qed.

Next Obligation.
  apply eqModb_ok; trivial.
Qed.


Definition eqModZb {M} (x y : Z) := (x mod (Zpos M) =? y mod (Zpos M))%Z.
