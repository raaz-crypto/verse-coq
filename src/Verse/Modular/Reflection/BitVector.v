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

(** * Bitvector operation without overflows

Given a bitvector expression e we want to show that that e as a
bitvector is the same as e as a N. The reified of such an expression
will be expressed as a sum of terms form.

 *)

Definition Term A := list A.

Definition termDenote {A} (u : A) (f : A -> A -> A) : Term A -> A
  := List.fold_right f u .

Definition bvTermDenote {sz} : Term (Bvector sz) -> Bvector sz
  := termDenote 1 multiplication.

Definition NTermDenote : Term N -> N := termDenote 1%N N.mul.

Hint Unfold termDenote bvTermDenote NTermDenote N.pow Pos.pow : bitvector_reflection.

(**
ATerm stands for additive term. An additive term is just a "sum" of
Terms (multiplicative)
*)
Definition ATerm A := Term (Term A).

Definition mapAterm {A B}(f : A -> B) : ATerm A -> ATerm B
  := List.map (List.map f).


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




Add Ring bit_arith_ring : (ArithRing.bit_arithm_ring 1).
Print Rings.
Goal forall x y : Bvector 2, Bv2N (x + y) = Bv2N (y + x).
  intros x y.
  simplify 2 (x + y).
  simplify 2 (y + x).
  repeat (rewrite denote_spec).
  autounfold with bitvector_reflection; simpl.
  unfold Pos.pow.
  match goal with
  | [ |- (?X mod _ = ?Y mod _)%N ] => assert (X = Y)
  end.
  ring.
  rewrite H; trivial.
Qed.
