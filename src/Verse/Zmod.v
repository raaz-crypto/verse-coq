Require Import ZArith.
Require Import Setoid.

Declare Scope zmod2_scope.
Delimit Scope zmod2_scope with Zmod2.

Inductive Zmod2 : nat -> Set := zmod2 : forall {n}, Z -> Zmod2 n.
Bind Scope zmod2_scope with Zmod2.

Definition reduce n (z : Z) : Z := z mod two_power_nat n.

Section ModularZ.
  Context {n : nat}.

  Definition to_Z (x : Zmod2 n) : Z :=
    match x with
    | zmod2 z => reduce n z
    end.

  Definition of_Z (z : Z) : Zmod2 n :=
    zmod2 (reduce n z).

  Definition eqmod (x y : Zmod2 n) : Prop :=
    match x, y with
    | zmod2 z1 , zmod2 z2 => reduce n z1 = reduce n z2
    end.
  Definition eqb (x y : Zmod2 n) : bool :=
    match x, y with
    | zmod2 z1, zmod2 z2 => Z.eqb (z1 mod two_power_nat n) (z2 mod two_power_nat n)
    end.
  Definition binOp (f : Z -> Z -> Z) (x y : Zmod2 n) : Zmod2 n :=
    match x, y with
    | zmod2 z1 , zmod2 z2 => of_Z (f z1 z2)
    end.
  Definition uniOp (f : Z -> Z) (x : Zmod2 n) : Zmod2 n :=
    match x with
    | zmod2 z => of_Z (f z)
    end.
  Definition add := binOp Z.add.

  Definition mul := binOp Z.mul.
  Definition sub := binOp Z.sub.
  Definition opp := uniOp Z.opp.
  Definition zero := of_Z  0%Z.
  Definition one  := of_Z  1%Z.
End ModularZ.

Infix "==" := (@eqmod _) (at level 70, no associativity): zmod2_scope.
Infix "==?" := (@eqb _) (at level 70, no associativity): zmod2_scope.
Notation "0" := zero : zmod2_scope.
Notation "1" := one  : zmod2_scope.
Infix "+" := (add) : zmod2_scope.
Infix "*" := (mul) : zmod2_scope.
Infix "-" := (sub) : zmod2_scope.



Ltac crush_modular :=
  repeat match goal with
         | [ H : Zmod2 _ |- _ ] => destruct H; simpl
         | [ |- (_ == _)%Zmod2 -> _ ] => simpl;  intro
         | [ |- _ -> _ ] => simpl ; intro
         | [ H : _ = _ |- _ = _ ] => inversion H; easy
         | _ => unfold eqmod; unfold of_Z; unfold to_Z; autorewrite with zmodrewrites; eauto with zmodfacts
         end.

Lemma reduce_idem : forall n z, reduce n (reduce n z) = reduce n z.
    intros;
    unfold reduce;
    rewrite Z.mod_mod; easy.
Qed.

Hint Rewrite reduce_idem  : zmodrewrites.

Lemma reduce_add : forall n z0 z1, reduce n (z0 + z1) = reduce n (reduce n z0 + reduce n z1).
  intros.
  unfold reduce.
  rewrite Z.add_mod; easy.
Qed.

Lemma reduce_minus : forall n z0 z1, reduce n (z0 - z1) = reduce n (reduce n z0 - reduce n z1).
  intros.
  unfold reduce.
  rewrite Zminus_mod; easy.
Qed.
Lemma reduce_mul : forall n z0 z1, reduce n (z0 * z1) = reduce n (reduce n z0 * reduce n z1).
  intros.
  unfold reduce.
  rewrite Z.mul_mod; easy.
Qed.

Hint Resolve reduce_add reduce_mul : zmodfacts.


Lemma reduce_opp n : forall z, reduce n (- z ) = reduce n (0 - reduce n z).
  intro.
  unfold reduce.
  rewrite <- Z.sub_0_l.
  rewrite Zminus_mod_idemp_r. easy.
Qed.

Lemma reduce_add_l n : forall z0 z1, reduce n (z0 + reduce n z1) = reduce n (z0 + z1).
  intros.
  rewrite reduce_add.
  crush_modular.
Qed.

Lemma reduce_add_r n : forall z0 z1, reduce n (reduce n z0 + z1) = reduce n (z0 + z1).
  intros.
  rewrite reduce_add.
  crush_modular.
Qed.

Lemma reduce_mul_l n : forall z0 z1, reduce n (z0 * reduce n z1) = reduce n (z0 * z1).
  intros.
  rewrite reduce_mul.
  crush_modular.
Qed.

Lemma reduce_mul_r n : forall z0 z1, reduce n (reduce n z0 * z1) = reduce n (z0 * z1).
  intros.
  rewrite reduce_mul.
  crush_modular.
Qed.

Hint Rewrite reduce_add_r reduce_add_l
     reduce_mul_r reduce_mul_l
  : zmodrewrites.


Section ModularZFacts.

  Context {n : nat}.
  Lemma eqb_eq : forall (x y : Zmod2 n), ((x ==? y) = true <-> x == y)%Zmod2.
    crush_modular.
    rewrite Z.eqb_eq; intuition.
  Qed.

  Lemma eqmod_refl : reflexive (Zmod2 n) (@eqmod n).
    unfold reflexive.
    crush_modular.
  Qed.
  Lemma eqmod_sym : symmetric (Zmod2 n) (@eqmod n).
    unfold symmetric.
    crush_modular.
  Qed.
  Lemma eqmod_transitive : transitive (Zmod2 n) (@eqmod n).
    unfold transitive.
    crush_modular.
  Qed.
End ModularZFacts.

Add Parametric Relation n : (Zmod2 n) (@eqmod n)
    reflexivity proved by (@eqmod_refl n)
    symmetry proved by (@eqmod_sym n)
    transitivity proved by (@eqmod_transitive n) as modular_arithmetic_equality.
Add Parametric Morphism n : (@add n)
    with signature @eqmod n ==> @eqmod n ==> @eqmod n as modular_addition_morphism.
  crush_modular.
  rewrite reduce_add.   rewrite H; rewrite H0.
  rewrite <- reduce_add; easy.
Qed.


Add Parametric Morphism n : (@mul n)
    with signature @eqmod n ==> @eqmod n ==> @eqmod n as modular_multiplication_morphism.
  crush_modular.
  rewrite reduce_mul; rewrite H; rewrite H0.
  rewrite <- reduce_mul; easy.
Qed.

Add Parametric Morphism n : (@opp n)
    with signature @eqmod n ==> @eqmod n as modular_op_morphism.
  crush_modular.
  rewrite reduce_opp.
  rewrite H.
  rewrite <- reduce_opp.
  trivial.
Qed.


Program Definition zmod_arithm_ring n
  : ring_theory
      (@zero n)
      (@one n)
      (@add n)
      (@mul n)
      (@sub n)
      (@opp n)
      (@eqmod n)
  := _.
Next Obligation.
  apply mk_rt; crush_modular.
  rewrite Z.add_comm; crush_modular.
  rewrite Z.add_assoc; crush_modular.
  rewrite Z.mul_1_l; crush_modular.
  rewrite Z.mul_comm; crush_modular.
  rewrite Z.mul_assoc; crush_modular.
  rewrite Z.mul_add_distr_r; crush_modular.
  rewrite Z.add_opp_diag_r; crush_modular.
Defined.


Program Definition z_to_zmod_morph n : ring_morph 0%Zmod2 1%Zmod2 (@add n) (@mul n) (@sub n) (@opp n) (@eqmod n)
                                                  0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb of_Z :=
  _.
Next Obligation.
  apply mkmorph; crush_modular; simpl; repeat crush_modular.
  rewrite reduce_minus; crush_modular.
  rewrite reduce_opp. crush_modular.
  assert (xEqY: x = y) by (rewrite <- Z.eqb_eq; easy).
  crush_modular.
Qed.

Section Test.
  Variable n : nat.
  Definition the_ring := zmod_arithm_ring n.
  Add Ring zmod_ring : (zmod_arithm_ring n) (morphism (z_to_zmod_morph n)).

  Lemma modi_formula : forall a b : Zmod2 n, ((a + b) * (a + b) == a * a + b * b + (of_Z 2) * a * b)%Zmod2.
    intros.
    ring_simplify. ring.
  Qed.
End Test.
