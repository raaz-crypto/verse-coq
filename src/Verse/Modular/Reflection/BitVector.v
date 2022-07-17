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
the equation v = F(v₁,...,vₙ), where v and vᵢ's are bit vectors of
size s and F is a polynomial, we want to prove that Bv2N v = F ( Bv2N
v₁ , ..., Bv2N vₙ). We are actually given bounds on Bv2N vᵢ.

The proof strategy

1. Prove that Bv2N v = F (Bv2N vᵢ,..., Bv2N vₙ) mod 2ˢ.

2. Prove that F(Bv2N vᵢ ..., Bv2N vₙ) < 2ˢ.

 *)

(** ** Sum of product polynomials.

The main idea behind the bit size of F(x₁,....,xₙ) in terms of the bit
sizes the individual xᵢ's is the following two rules

1. bitsize(a * b) ≤ bitsize (a) + bitsize (b)

2. bitsize (a + b) ≤ max( bitsize(a) , bitsize(b)) + 1

While the inequality 1 is the best we can do when it comes to
multiplication, in terms of addition the inequality 2 leads to too
loose a bound. The inequality will give bitsize( ∑ᵢⁿ aᵢ ) ≤ maxᵢ
(bitsize (aᵢ)) + n where as we know that ∑ᵢⁿ aᵢ ≤ n max(aᵢ) and hence
bitsize ( ∑ᵢⁿ aᵢ) ≤ bitsize (n . max(aᵢ) ) ≤ N.size n +
max(bitsize(aᵢ)), which is much better.

Therefore we would like our summations to be as flat as
possible. Henceforth, we only consider sum of product form for our
polynomial. We will represent this using ATerm.

*)

Definition Term A := list A.
Definition ATerm A := Term (Term A).

(** The map function for ATerms. For terms it is just the list map *)
Definition mapAterm {A B}(f : A -> B) : ATerm A -> ATerm B
  := List.map (List.map f).


Definition termDenote {A} (u : A) (f : A -> A -> A) : Term A -> A
  := List.fold_right f u.

Definition bvTermDenote {sz} : Term (Bvector sz) -> Bvector sz
  := termDenote 1 multiplication.

Definition NTermDenote : Term N -> N := termDenote 1%N N.mul.
Hint Unfold termDenote bvTermDenote NTermDenote N.pow Pos.pow : bitvector_reflection.


Definition bvDenote {sz} (atrm : ATerm (Bvector sz)): Bvector sz
  := termDenote 0 addition (List.map bvTermDenote atrm).

Definition NDenote (atrm : ATerm N) : N
  := termDenote 0%N N.add (List.map NTermDenote atrm).

Hint Unfold bvDenote NDenote : bitvector_reflection.


Lemma termDenote_spec {sz} : forall t : Term (Bvector sz), Bv2N (bvTermDenote  t) <==[mod 2^N.of_nat sz ] NTermDenote (List.map (@Bv2N sz) t).
  intro t.
  unfold redMod.
  unfold bvTermDenote.
  unfold NTermDenote.
  unfold multiplication.
  induction t as [|x xs IHt]; simpl; eauto with bitvector_reflection.
  - rewrite Bv2N_mul_mod;
      rewrite IHt;
      rewrite N.mul_mod_idemp_r; eauto with bitvector_reflection.
Qed.

Lemma denote_spec {sz} : forall atrm : ATerm (Bvector sz), Bv2N (bvDenote  atrm) <==[mod 2^N.of_nat sz ] NDenote (mapAterm (@Bv2N sz)  atrm).
  intro atrm.
  unfold redMod.
  unfold bvDenote.
  unfold NDenote.
  unfold addition.
  induction atrm as [|x xs IH] ; simpl; eauto with bitvector_reflection.
  - rewrite Bv2N_plus_mod.
    rewrite IH.
    rewrite termDenote_spec.
    rewrite <- N.add_mod; eauto with bitvector_reflection.
Qed.



Ltac reifyTerm sz e :=
  match e with
  | multiplication ?e1 ?e2 => let e1p := reifyTerm sz e1 in
                             let e2p := reifyTerm sz e2 in
                             constr:((e1p ++ e2p)%list : Term (Bvector sz) )
  | _ => constr:(cons e  nil)
  end.

Ltac reify sz e :=
  match e with
  | ?e1 + ?e2 => let e1p := reify sz e1 in
                let e2p := reify sz e2 in
                constr:((e1p ++ e2p)%list : ATerm (Bvector sz) )
  | _ => let ep := reifyTerm sz e in constr:(cons ep nil)
  end.

Require Verse.BitVector.ArithRing.
Ltac simplify sz e := let atrm := reify sz e in
                      let H := fresh "HReify" in
                      assert (H:e = bvDenote atrm) by (
                          try (autounfold with bitvector_reflection; simpl; ring);
                          fail "Bitvector ring for size " sz "probably not in scope;"
                            "use Add Ring foo : " "ArithRing.bit_arithm_ring ..."
                            "(cf Verse.BitVector.ArithRing)"
                        );
                      rewrite H.




(** ** Bounded quantities.

To prove the size inequality, we would need to additionally keep track
of the sizes. For this we have the bounded variants BBvector and BN of
Bvector and N respectively.

 *)

Module Bounded.

  Inductive t A (sizeFn : A -> N) :=
  | bounded   : forall a n, (sizeFn a <= n)%N -> t A sizeFn
  | unbounded : A -> t A sizeFn.

  Arguments bounded {A sizeFn}.
  Arguments unbounded {A sizeFn}.

  Definition BBvector sz := t (Bvector sz) BVN_size.

  Definition BN := t N N.size.

  Definition BBv2N {sz} (bv : BBvector sz) : BN :=
    match bv with
    | bounded vec n pf => bounded (Bv2N vec) n pf
    | unbounded vec    => let n := Bv2N vec in
                       bounded n (N.size n) (N.le_refl (N.size n))
    end.

  Ltac reifyTerm sz e :=
    match e with
    | multiplication ?e1 ?e2 => let e1p := reifyTerm sz e1 in
                               let e2p := reifyTerm sz e2 in
                               constr:((e1p ++ e2p)%list : Term (BBvector sz) )
    | _ => match goal with
          | [ pf : BVN_size e < ?n |-  _ ] => let ep := constr:(bounded e n pf) in
                                        constr:(cons ep nil)
          | _ => constr:(cons (unbounded e)  nil)
          end
    end.

  Ltac reify sz e :=
    match e with
    | ?e1 + ?e2 => let e1p := reify sz e1 in
                  let e2p := reify sz e2 in
                  constr:((e1p ++ e2p)%list : ATerm (BBvector sz) )
    | _ => let ep := reifyTerm sz e in constr:(cons ep nil)
    end.

End Bounded.

(** * Testing and illustration here *)


Add Ring bit_arith_ring : (ArithRing.bit_arithm_ring 1).
Print Rings.
Goal forall x y : Bvector 2, Bv2N (x + y) = Bv2N (y + x).
  intros x y.
  simplify 2 (x + y).
  simplify 2 (y + x).
  repeat (rewrite denote_spec).
  autounfold with bitvector_reflection; simpl.
  match goal with
  | [ |- (?X mod _ = ?Y mod _)%N ] => assert (X = Y)
  end.
  ring.
  rewrite H; trivial.
Qed.
