(**

We begin with a different representation of polynomials which is much
more convenient to work with when it comes to karatsuba's algorithm.
We start with defining a complete binary tree of depth n.

The type kpoly A n captures polynomials of degree 2ⁿ -1 with
coefficients over A.

 *)



Inductive tree (A : Type) : nat -> Type :=
| leaf : A -> tree A 0
| node : forall n, tree A n -> tree A n -> tree A (S n).


Arguments leaf {A}.
Arguments node [A n].
(* If a coefficient is None, then it is zero *)
Definition kpoly A n := tree (option A) n.

Fixpoint kzero (A : Type) (n : nat) :=
  match n with
  | 0 => leaf (@None A)
  | S m => let kn := kzero A m
          in node kn kn
  end.

Require Import List.
Require Import Verse.CryptoLib.Polynomials.
Require Import Arith.

Import ListNotations.
(** The meaning of kpoly in terms of actual polynomials *)

Fixpoint denote {A n} (kp : kpoly A n) : poly A :=
  match kp with
  | leaf (Some coef) => [ (coef,0) ]
  | leaf None        => []
  | node kp1 kp2  => Polynomials.add (denote kp1) (xpownTimes (2^n) (denote kp2))
  end.


Definition up {n} {A : Type}(kp : kpoly A n) : kpoly A (S n) :=
  node kp (kzero A n).

Definition xPow2Pow n {A : Type}(kp : kpoly A n) : kpoly A (S n) :=
  node (kzero A n) kp.

Require Import Arith.
Require List.
Import List.ListNotations.

Section Evaluation.

  Context {SR : Type}`{Semi_Ring SR}.

  Fixpoint eval {n} (eta : SR)(kp : kpoly SR n) : SR :=
    match kp with
    | leaf None =>  0%ring
    | leaf (Some x)  => x
    | node  kp1 kp2 => (eval eta kp1 + eta^(2^n) * eval eta kp2)%ring
    end.

End Evaluation.

Ltac crush_kpoly := repeat (Polynomials.crush_poly;
                            match goal with
                            | [ coef : option _ |- _ ] => destruct coef
                            | [ n : nat |- _ ] => try (ring_simplify (2^n + (2^n + 0)))
                            | _ => idtac
                            end).

Ltac induct_on kp :=
  induction kp as [coef | kp1 kp2 iHkp]; crush_kpoly.
Section Correctness.

  Context {eta : nat}.

  Lemma denote_spec : forall n (kp : kpoly nat n), eval eta kp = Polynomials.eval eta (denote kp).
    intros.
    induct_on kp.
  Qed.

  Lemma kzero_spec : forall n, eval eta (kzero nat n) = 0.
    intro n.
    induction n; crush_kpoly.
    rewrite IHn; crush_kpoly.
  Qed.

  Lemma up_spec : forall n  (kp : kpoly nat n), eval eta (up kp) = eval eta kp.
    intros n.
    induction n.
    intro kp. destruct kp.
    - destruct o; simpl; specialise_to_nat; ring.
    - unfold up. simpl. rewrite kzero_spec.
      ring_simplify (2^n + (2^n + 0)); specialise_nat_ring.
    - intro kp; destruct kp. unfold up; destruct o; simpl; specialise_to_nat; ring.
      unfold up; simpl; repeat (specialise_to_nat). ring_simplify (2^n0 + (2^n0 + 0)).

  Lemma constCoef_spec : forall kp : kpoly nat 0, eval eta kp = constCoef kp;
    intro kp.
    inversion kp.

  Lemma add_spec :  forall n (kp1 kp2 : kpoly nat n),
      eval eta (add kp1 kp2)
      = eval eta kp1 + eval eta kp2.
    intros n kp1.
    induction kp1.
    - simpl; trivial.
    - simpl; intro kp2. inversion kp2.
      simpl.
Polynomials.eval eta
                    (Polynomials.add (denote kp1) (denote kp2)).
    intros. induction kp1.
    induction kp2; simpl; trivial; specialise_to_nat.
    - ring.
    - ring_simplify (2^n + 0).
End Correctness.

Require Import Verse.CryptoLib.Polynomials.
Section Arithmetic.
  Context {SR : Type}`{Semi_Ring SR}.

  Fixpoint constCoef {n}(kp : kpoly SR n) : SR :=
    match kp with
    | kzero    => 0%ring
    | kconst a => a
    | ksplit k1 _ => constCoef k1
    end.

  Fixpoint add {n} (kpA : kpoly SR n) : kpoly SR n -> kpoly SR n :=
    match kpA with
    | kzero => fun kpB => kpB
    | kconst a => fun kb => kconst (a + constCoef kb)%ring
    | ksplit kA1 kA2 => fun kB => let (kB1 , kB2) := kChildren kB in
                              ksplit (add kA1 kB1) (add kA2 kB2)
    end.
