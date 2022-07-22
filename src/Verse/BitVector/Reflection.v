(* begin hide *)
Require Import NArith.
Require Import BinNat.
Require Import Verse.BitVector.
Require Import Verse.BitVector.Facts.
Require Import Verse.Modular.Equation.


Create HintDb bitvector_reflection.
Lemma two_power_non_zero : forall n : N, (2^n)%N <> 0%N.
  intro n.
  apply N.pow_nonzero; intro H; inversion H.
Qed.

#[local] Hint Resolve two_power_non_zero @Bv2N_N2Bv_sized_mod : bitvector_reflection.

(* end hide *)

(** * Bitvectors operations without overflows

The basic idea here is that bitvector arithmetic is the same as the
corresponding N arithmetic as long as there are no overflows. Given
the equation [v = F(v₁,...,vₙ)], where [v] and [vᵢ]'s are bit vectors
of size [s] and [F], a polynomial, we want to prove that [Bv2N v = F
(Bv2N v₁ , ..., Bv2N vₙ)]. This is not in general true due to
overflows and the best we can do is to prove the following modular
equation.

* [Bv2N v = F (Bv2N vᵢ,..., Bv2N vₙ) mod 2ˢ].

However, if the individual [vᵢ]'s are such that the quantities [Bv2N
vᵢ] are sufficiently upper bounded, we can prove the following bound
as well

* [F(Bv2N v₁ ..., Bv2N vₙ) < 2ˢ].

This together with the above modular equation gives us the desired
arithmetic identity

* [Bv2N v = F (Bv2N vᵢ,..., Bv2N vₙ)].

This module gives reflection based tactics for proving such
identities. These identities are required to prove the correctness of
bignum multiplications where the total bits are broken up in to limbs
of appropriate sizes.

 *)


(** ** Binary Nats with bounds

An important ingredient in our tactics is arithmetic expressions
involving binary nats with bounds. We capture them here.

 *)

(* begin hide *)
Require Import Psatz.

(* end hide *)

Inductive BN :=
| bounded : forall (n bnd : N), (n < bnd)%N -> BN.


Program Definition injB (n : N) : BN :=
  bounded n (N.succ n) _.

Next Obligation.
  lia.
Qed.

(** Forget the bound *)
Definition forget (bn : BN) : N :=
  match bn with
  | bounded n _ _ => n
  end.

(** Get the bound on the value *)

Definition boundOf (bn : BN) : N :=
  match bn with
  | bounded _ bnd _ => bnd
  end.

(** Get the bound proof *)
Definition boundProof (bn : BN) : (forget bn < boundOf bn)%N
  := match bn with
     | bounded _ _ pf => pf
     end.

Require Import NFacts.
Require Import setoid_ring.Algebra_syntax.


#[export] Instance zero_BN : Zero BN := injB 0%N.
#[export] Instance one_BN : One BN := injB 1%N.

#[export] Program Instance add_BN : Addition BN :=
  fun x y => match x, y with
          | bounded a n pfx, bounded b m pfy => bounded (a+b)%N (n+m)%N _
          end.

Next Obligation.
  eauto with Nfacts.
Qed.

#[export] Program Instance mul_BN : @Multiplication BN BN :=
  fun x y => match x, y with
          | bounded a n pfx, bounded b m pfy => bounded (a*b)%N (n*m)%N _
          end%N.

Next Obligation.
  eauto with Nfacts.
Qed.

(** Finally, we define algebra syntax for N which will make some of
    our reification code easier

TODO: We may want to make the exports of this local if the tactics
work in other modules that import this one.

 *)

#[export] Instance zero_N : Zero N := 0%N.
#[export] Instance one_N  : One N := 1%N.
#[export] Instance add_N  : Addition N := N.add.
#[export] Instance mul_N  : Multiplication := N.mul.


(** * Reified expressions of a

As with all reflection based proofs, we need a ast to which terms have
to be reified. In our case it is a simple expression ast with only
addition an multiplication involved. A point to note here is that we
do not have subtraction in the structure; this is because subtraction
can easily make all the bounds of the individual bitvectors irrelevant
and hence cannot be handled by our tactics. We can still use these
tactics by the following method.

Let v = F(v₁....,vₙ) be the desired equation that we want to work
with. We first prove that [F(x₁...,xₙ) = G(x₁,...,xₙ)] for all
bitvectors x₁,...,xₙ where the polynomial [G] does not involve
substraction. We then use G instead of F for carrying out our
computation.

*)

Module Exp.

  Inductive t A :=
  | Const : A -> t A
  | Plus  : t A -> t A -> t A
  | Mul   : t A -> t A -> t A.

  Arguments Const {A}.
  Arguments Plus {A}.
  Arguments Mul {A}.


  Fixpoint map {A B}(f : A -> B)(e : t A) : t B :=
    match e with
    | Const a      => Const (f a)
    | Plus  e1 e2  => Plus (map f e1) (map f e2)
    | Mul e1 e2 => Mul (map f e1) (map f e2)
    end.

  Fixpoint denote {A}`{Addition A}`{@Multiplication A A} (e : t A) : A :=
    match e with
    | Const a => a
    | Plus e1 e2 => denote e1 + denote e2
    | Mul e1 e2 => denote e1 * denote e2
    end.

  #[export] Instance add_exp A : Addition (t A) := Plus.
  #[export] Instance mul_exp A : @Multiplication (t A) (t A):= Mul.

End Exp.
Import Exp.

Lemma forget_denote_comm  : forall e : t BN, denote (map forget e) = forget (denote e).
  intros.
  induction e as [|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2 ]; simpl; trivial.
  - rewrite IHe1.
    rewrite IHe2.
    set (de1:=denote e1). set (de2:=denote e2).
    destruct de1.
    destruct de2.
    simpl; trivial.
  - rewrite IHe1.
    rewrite IHe2.
    set (de1 := denote e1); set (de2:= denote e2);
      destruct de1; destruct de2; simpl; trivial.
Qed.

Lemma Bv2N_denote_map_comm_mod {sz} : forall e : t (Bvector sz), Bv2N (denote e) = (denote (map (@Bv2N sz) e) mod 2^N.of_nat sz)%N.
Proof.
  intros e.
  induction e as [|e1 IH1 e2 IH2| e1 IH1 e2 IH2]; simpl.
  - rewrite N.mod_small; eauto with bitvector.
  - unfold addition; rewrite Bv2N_plus_mod; rewrite IH1; rewrite IH2; simpl;
      rewrite <- N.add_mod; eauto with bitvector. eauto with Nfacts.
  - unfold multiplication; rewrite Bv2N_mul_mod; rewrite IH1; rewrite IH2; simpl;
      rewrite <- N.mul_mod; eauto with bitvector; eauto with Nfacts.
Qed.


Module Tactics.
  (** The generalised reification tactic that reifies to a give type B
      We want Addition and Multiplication instances to be defined for the
      type B. The const is a tactic that deals with the base case.
   *)
  Ltac reifyTo B const e :=
    match e with
    | (?e1 + ?e2) =>
        let e1p := reifyTo B const e1 in
        let e2p := reifyTo B const e2 in
        constr:(e1p + e2p : B)

    | (?e1 * ?e2) =>
        let e1p := reifyTo B const e1 in
        let e2p := reifyTo B const e2 in
        constr:(e1p * e2p : B)
    | _ => const e
    end.

  (** This tactic creates the arithmetic version of a given expression *)
  Ltac arithm e :=
    let const e := constr:(Bv2N e) in
    reifyTo N const e.

  (** This tactic creates the bounded arithmetic version of a given expression *)
  Ltac reifyBNE e :=
    let const e := match goal with
                   | [ H : (e < ?bnd)%N |- _ ] => constr:(Const (bounded e bnd H : BN ) )
                   | _ => constr:(Const (injB e : BN))
                   end in
    reifyTo (Exp.t BN) const e.

  (** This reifies a given expression into the expression tree *)
  Ltac reify e sz :=
    let const x := constr:(Const x) in
    reifyTo (Exp.t (Bvector sz)) const e.

  (** Overall approach

  Given the expression Bv2N poly(v₁...,vₙ), the arithmetic version of
  it is poly(Bv2N v₁,....,Bv2N vₙ).  The arithmetic assertion
  essentially proves Bv2N poly(v₁,....,vₙ) = poly (Bv2N v₁,.., Bv2N
  vₙ).

  The overall method is as follows.


  - Goal e = ae  (where ae is the arithmetic version of e)
    + Goal e = ae mod 2ˢᶻ
      - Goal e = denote (Re) (where Re is the reified expression)
             ae = denote (map Bv2N Re)
        And use the lemma denote (Re) = denote (map (Bv2N Re) mod 2ˢᶻ


    + Goal ae = ae mod 2ˢᶻ
      - Goal ae = forget (denote (RAe)) where RAE is the reified expression
                       associated with

   *)

  Ltac crush_modular e eA sz :=
    let HR := fresh "HReify" in
    let HA := fresh "HReifyA" in
    let Re := reify e sz in
    assert (HR: e = denote Re) by (simpl; trivial);
    assert (HA: eA = denote (map (@Bv2N sz) Re)) by (simpl; trivial);
    rewrite HR; rewrite HA; try apply Bv2N_denote_map_comm_mod.

  Ltac crush_ineq :=
    match goal with
    |  [ |- (?E < ?M)%N  ] =>
         let HR    := fresh "HReify" in
         let Hineq := fresh "Hineq" in
         let Re := reifyBNE E in
         let bExp  := constr:(denote Re) in
         assert (HR: E = forget (bExp)) by (simpl; trivial);
         assert (Hineq: (E < boundOf(bExp))%N) by (rewrite HR; exact (boundProof bExp));
         apply (N.lt_trans _ _ _ Hineq); simpl; lia
    end.

  Ltac assert_arithmetic e sz :=
    let eA := arithm e in
    let HArithm := fresh "HArithm" in
    assert(HArithm:Bv2N e = eA) by
      let HM := fresh "HM" in
      assert (HM: Bv2N e <==[mod 2^N.of_nat sz] eA) by crush_modular e eA sz;
      rewrite HM; apply N.mod_small;
      crush_ineq.




End Tactics.



Definition base : N := 65536.

Definition toN3 {sz} (a b c : Bvector sz) : N :=
  (Bv2N a + base * Bv2N b + base * base * Bv2N c)%N.

Definition toN2 {sz}  (a b : Bvector sz) : N :=
  (Bv2N a + base * Bv2N b)%N.


Goal forall a0 a1 b0 b1 : Bvector 64, (Bv2N a0 < 2^16)%N -> (Bv2N a1 < 2^16)%N ->
                                 (Bv2N b0 < 2^16)%N -> (Bv2N b1 < 2^16)%N ->
    (toN2 a0 a1 * toN2 b0 b1)%N = toN3 (a0 * b0) (a0 * b1 + a1 * b0) (a1 * b1).

  intros.
  Unset Ltac Debug.
  Tactics.assert_arithmetic (a0 * b0) 64.
  Tactics.assert_arithmetic (a0 * b1 + a1 * b0) 64.
  Tactics.assert_arithmetic (a1 * b1) 64.
  unfold toN2.
  unfold toN3.
  rewrite HArithm.
  rewrite HArithm0.
  rewrite HArithm1.
  (* TODO: unfortunate clash of notation *)
  unfold multiplication; unfold addition. unfold mul_N; unfold add_N.
  ring.
Qed.
