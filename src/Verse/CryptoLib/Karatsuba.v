(**

We begin with a different representation of polynomials which is much
more convenient to work with when it comes to karatsuba's algorithm.
The type kpoly A n captures polynomials of degree 2ⁿ -1 with
coefficients over A.

 *)

Inductive kpoly (A : Type) : nat -> Type :=
| kzero  : forall n , kpoly A n
| kconst : A -> kpoly A 0
| ksplit : forall n, kpoly A n -> kpoly A n -> kpoly A (S n).


Arguments kzero {A n}.
Arguments kconst {A}.
Arguments ksplit [A n].

Require Import Verse.CryptoLib.Polynomials.
Require Import Arith.
Require List.
Import List.ListNotations.

(** The meaning of kpoly in terms of actual polynomials *)

Fixpoint denote {A n} (kp : kpoly A n) : poly A :=
  match kp with
  | kzero => []
  | kconst x => [(x,0)]
  | ksplit kp1 kp2 => Polynomials.add (denote kp1) (xpownTimes (2^n) (denote kp2))
  end.

Section Evaluation.

  Context {SR : Type}`{Semi_Ring SR}.

  Fixpoint eval {n} (eta : SR)(kp : kpoly SR n) : SR :=
    match kp with
    | kzero => semi_ring_zero
    | kconst x => x
    | ksplit kp1 kp2 => (eval eta kp1 + eta^(2^n) * eval eta kp2)%ring
    end.

End Evaluation.


Section Correctness.

  Context {eta : nat}.

  Lemma denote_spec : forall n (kp : kpoly nat n), eval eta kp = Polynomials.eval eta (denote kp).
    intros.
    induction kp; simpl; trivial;
    specialise_to_nat.
    ring.
    rewrite power_lemma;
    simpl; rewrite <- add_spec.
    rewrite xpownTimes_eval.
    repeat(rewrite Nat.pow_add_r).
    rewrite <- IHkp1.
    rewrite <- IHkp2.
    trivial.
  Qed.

End Correctness.
