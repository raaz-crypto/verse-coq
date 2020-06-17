(** * Facts about bitvector operations

Cryptographic implementations often make use bitwise operations
liberally. This module collects a bunch of facts that can be used to
prove the correctness of such algorithms.

- Commutativity, Associativity and distributive properties of bitwise
  and, or and xor operations.

- Arithmetic facts like [BV2N_shiftR_mod].


*)

(* begin hide *)
Require Import BinNat.
Require Import NArith.
Require Import Arith.
Require Import Verse.BitVector.
Require Import Verse.NFacts.

Hint Resolve
     andb_comm andb_assoc andb_orb_distrib_r
     orb_comm orb_assoc orb_andb_distrib_r
     xorb_comm xorb_assoc
: bitvector.

Hint Rewrite andb_true_r  orb_false_r  xorb_true_r xorb_false_r xorb_true_l xorb_false_l : bitvector.

Hint Rewrite
     Nat.sub_0_r Nat.sub_diag Nat.mod_0_l Nat.mod_mod
     Nat.double_twice Nat.div2_succ_double Nat.div2_double
     Nat.add_1_r Nat.add_0_r Nat.add_0_l
  : bitvector.




Hint Unfold BVshiftR BVshiftL : bitvector.

Module Internal.
  Lemma vector_0_nil : forall A (vec : Vector.t A 0), vec = [].
  Proof.
    intro A.
    exact (Vector.case0 (fun v => v = []) eq_refl).
  Qed.

  Lemma vector_cons_equation {A} {a1 a2 : A} {n} {v1 v2 : Vector.t A n}:
    a1 = a2 -> v1 = v2 -> a1 :: v1 = a2 :: v2.
  Proof.
    intros H1 H2.
    rewrite H1. rewrite H2.
    trivial.
  Qed.


  Lemma iter_id : forall A n x, Nat.iter n (@id A) x = x.
    induction n; trivial.
  Qed.



  Lemma iter_0 : forall A (f : A -> A)(x : A) , Nat.iter 0 f x = x.
    intros. trivial.
  Qed.

  Lemma iter_add : forall A (f : A -> A) m n a0, Nat.iter m f (Nat.iter n f a0) = Nat.iter (m+n) f a0.
  Proof.
    intros A f m n a0.
    induction m as [|k IHk]; simpl; trivial.
    rewrite IHk; trivial.
  Qed.

End Internal.

Import Internal.

Ltac crush := repeat (
                  unfold arithm;
                  try autorewrite with Nrewrites bitvector;
                  try eauto with Nfacts bitvector;
                  try simpl;
                  match goal with
                  | [ v : Bvector 0     |- _ ] => rewrite (vector_0_nil _ v)
                  | [ |- _ :: _ = _ :: _ ] => apply vector_cons_equation
                  | [ v : Bvector (S _) |- _ ]
                    => rewrite (Vector.eta v);
                      let h := fresh "h" in
                      let t := fresh "t" in
                      (generalize (Vector.hd v) as h;
                       generalize (Vector.tl v) as tl; intros h t)
                  | [ b : bool |- _ ] => destruct b
                  | _ => idtac
                  end
                ).





(** A more powerful induction

1. Apply induction on the given variable

2. Base case is crushed

3. The induction step is first softened by a crush then a rewrite by the Inductive hypothesis
 followed by crush.


*)

Ltac induct_on n :=
let m := fresh "m" in
let IHm := fresh "IHm" in
(induction n as [|m IHm]; crush; rewrite IHm; crush).


(** The vector variant of the induction *)
Ltac induct_on_vec v :=
let b := fresh "b" in
let sz := fresh "sz" in
let vec := fresh "vec" in
let IHvec := fresh "IHvec" in
(induction v as [|b sz vec IHvec]; crush; rewrite IHvec; crush).

(* end hide *)

(** * Shifts are homomorphisms.


The facts [BVshiftL_indentity], [BVshiftL_composition],
[BVshiftR_identity] and [BVshiftR_composition] shows that functions
[BVshiftL] as well as [BVshiftR] are homomorphisms from the monoid of
additive natural numbers to the monoid of functions on bitvectors
under compositions. The commutativity and associativity properties are
the corresponding properties in the image of these homomorphisms.

*)

Lemma BVshiftL_identity : forall sz (vec : Bvector sz),
  BVshiftL 0 vec = vec.
Proof.
  trivial.
Qed.

Lemma BVshiftL_composition : forall sz (vec : Bvector sz) n m,
    BVshiftL (n + m) vec = BVshiftL n (BVshiftL m vec).
Proof.
  intros sz vec n m.
  induct_on n.
Qed.


Lemma BVshiftR_identity : forall sz (vec : Bvector sz),
  BVshiftR 0 vec = vec.
Proof.
  trivial.
Qed.


Lemma BVshiftR_composition : forall sz (vec : Bvector sz) n m,
  BVshiftR (n + m) vec =  BVshiftR n (BVshiftR m vec).
Proof.
  intros sz vec n m.
  induct_on n.
Qed.

Lemma BVshiftL_commute : forall sz  (vec : Bvector sz) m n,
  BVshiftL m (BVshiftL n vec) = BVshiftL n (BVshiftL m vec).
Proof.
  intros.
    repeat rewrite <- BVshiftL_composition.
  rewrite Nat.add_comm; trivial.
Qed.

Lemma BVshiftL_assoc : forall sz (vec : Bvector sz) m n p,
  (fun v => BVshiftL m (BVshiftL n v)) (BVshiftL p vec) = BVshiftL m (BVshiftL n (BVshiftL p vec)).
Proof.
  intros; crush.
Qed.


Lemma BVshiftR_commute : forall sz  (vec : Bvector sz) m n,
  BVshiftR m (BVshiftR n vec) = BVshiftR n (BVshiftR m vec).
Proof.
  intros; repeat rewrite <- BVshiftR_composition.
  rewrite Nat.add_comm; trivial.
Qed.

Lemma BVshiftR_assoc : forall sz (vec : Bvector sz) m n p,
  (fun v => BVshiftR m (BVshiftR n v)) (BVshiftR p vec) = BVshiftR m (BVshiftR n (BVshiftR p vec)).
Proof.
  intros; crush.
Qed.

(* begin hide *)
Module BinOpInternals.

  Ltac map2_crush := try intros;
    rewrite <- Vector.eq_nth_iff;
    let p1 := fresh "p" in
    let p2 := fresh "p" in
    let eqHyp := fresh "eqHyp" in
    intros p1 p2 eqHyp; rewrite eqHyp;
    repeat rewrite (Vector.nth_map2 _ _ _ p2 p2 p2);
    repeat rewrite (Vector.nth_map _ _ p2 p2);
    autorewrite with bitvector; eauto with bitvector.

  Section BinOp.
    Variable A : Type.
    Variable op1 op2 : A -> A -> A.
    Variable op1_comm : forall (x y : A), op1 x y = op1 y x.
    Variable op1_assoc : forall x y z : A, op1 x (op1 y z) = op1 (op1 x y) z.
    Variable op1_op2_distr_r : forall a1 a2 a3, op1 a1 (op2 a2 a3) = op2 (op1 a1 a2)  (op1 a1 a3).



    Lemma map2_comm : forall sz (v1 v2 : Vector.t A sz),
        Vector.map2 op1 v1 v2 = Vector.map2 op1 v2 v1.
    Proof.
      map2_crush.
    Qed.

    Lemma map2_assoc : forall sz (u v w : Vector.t A sz),
        Vector.map2 op1 u (Vector.map2 op1 v w) =
        Vector.map2 op1 (Vector.map2 op1 u v) w.
    Proof.
      map2_crush.
    Qed.

    Lemma map2_distr : forall sz (u v w : Vector.t A sz),
        Vector.map2 op1 u (Vector.map2 op2 v w) =
        Vector.map2 op2 (Vector.map2 op1 u v) (Vector.map2 op1 u w).
    Proof.
      map2_crush.
    Qed.

  End BinOp.


  Lemma BVzeros_nth : forall sz (p : Fin.t sz), BVzeros [@p] = false.
  Proof.
    unfold BVzeros.
    unfold Bvect_false.
    intros; now rewrite Vector.const_nth.
  Qed.

  Lemma BVones_nth : forall sz (p : Fin.t sz), BVones [@p] = true.
  Proof.
    unfold BVones.
    unfold Bvect_true.
    intros; now rewrite Vector.const_nth.
  Qed.

End BinOpInternals.


Import BinOpInternals.
Hint Resolve map2_comm map2_assoc map2_distr : bitvector.
Hint Rewrite BVzeros_nth BVones_nth : bitvector.

(* end hide *)

(** ** Properties of bitwise and ,or and xor

The commutativity, associativity properties and existence of identity
for and, or and xor are proved as well as the distributivity of and
over or and vice-versa.

*)
Lemma BVand_0_r : forall sz (v  : Bvector sz), BVand v BVones = v.
Proof.
  unfold BVand; map2_crush.
Qed.


Lemma BVand_0_l : forall sz (v  : Bvector sz), BVand BVones v = v.
Proof.
  unfold BVand; map2_crush.
Qed.

Lemma BVand_comm : forall sz (v1 v2 : Bvector sz), BVand v1 v2 = BVand v2 v1.
Proof.
  unfold BVand.
  eauto with bitvector.
Qed.

Lemma BVand_assoc : forall sz (v1 v2 v3 : Bvector sz), BVand v1 (BVand v2 v3) = BVand (BVand v1 v2) v3.
Proof.
  unfold BVand.
  eauto with bitvector.
Qed.

Lemma BVor_0_r : forall sz (v  : Bvector sz), BVor v BVzeros = v.
Proof.
  unfold BVor; map2_crush.
Qed.

Lemma BVor_0_l : forall sz (v  : Bvector sz), BVor BVzeros v = v.
Proof.
  unfold BVor; map2_crush.
Qed.


Lemma BVor_comm : forall sz (v1 v2 : Bvector sz), BVor v1 v2 = BVor v2 v1.
Proof.
  unfold BVor.
  eauto with bitvector.
Qed.

Lemma BVor_assoc : forall sz (v1 v2 v3 : Bvector sz), BVor v1 (BVor v2 v3) = BVor (BVor v1 v2) v3.
Proof.
  unfold BVor.
  eauto with bitvector.
Qed.

(* ** Distributivity *)

Lemma BVor_and_distrib :
  forall sz (v1 v2 v3 : Bvector sz),
    BVor v1 (BVand v2 v3) = BVand (BVor v1 v2) (BVor v1 v3).
Proof.
  (*  intros sz v1 v2 v3. *)
  unfold BVor. unfold BVand.
  eauto with bitvector.
Qed.

Lemma BVand_or_distrib :
  forall sz (v1 v2 v3 : Bvector sz),
    BVand v1 (BVor v2 v3) = BVor (BVand v1 v2) (BVand v1 v3).
Proof.
  unfold BVor. unfold BVand.
  eauto with bitvector.
Qed.

Lemma BVxor_0_r : forall sz (v : Bvector sz), BVxor v BVzeros = v.
Proof.
  unfold BVxor.
  map2_crush.
Qed.

Lemma BVxor_0_l : forall sz (v : Bvector sz), BVxor BVzeros v = v.
Proof.
  unfold BVxor.
  map2_crush.
Qed.

Lemma BVxor_1_l : forall sz (v : Bvector sz), BVxor BVones v = BVcomp v.
Proof.
  unfold BVxor.
  unfold BVcomp.
  unfold Bneg.
  map2_crush.
Qed.

Lemma BVxor_1_r : forall sz (v : Bvector sz), BVxor v BVones = BVcomp v.
Proof.
  unfold BVxor.
  unfold BVcomp.
  unfold Bneg.
  map2_crush.
Qed.

Lemma BVxor_comm : forall sz (v1 v2 : Bvector sz), BVxor v1 v2 = BVxor v2 v1.
Proof.
  unfold BVxor.
  eauto with bitvector.
Qed.


Lemma BVxor_assoc : forall sz (v1 v2 v3 : Bvector sz), BVxor v1 (BVxor v2 v3) = BVxor (BVxor v1 v2) v3.
Proof.
  unfold BVxor.
  eauto with bitvector.
Qed.


(** ** Properties of rotation.

TODO: Some obvious properties are not yet proved.

*)

Lemma BVrotR_0 : forall sz (vec : Bvector sz),
    BVrotR 0 vec = vec.
Proof.
  crush.
Qed.

Lemma BVrotR_add : forall sz m n (vec : Bvector sz),
    BVrotR m (BVrotR n vec) = BVrotR (m + n) vec.
Proof.
  intros.
  unfold BVrotR.
  apply iter_add.
Qed.

Lemma BVrotL_0 : forall sz (vec : Bvector sz),
    BVrotL 0 vec = vec.
Proof.
  trivial.
Qed.

Lemma BVrotL_add : forall sz m n (vec : Bvector sz),
    BVrotL m (BVrotL n vec) = BVrotL (m + n) vec.
Proof.
  intros.
  unfold BVrotL.
  apply iter_add.
Qed.

Lemma popout_shiftin : forall sz x (xs : Bvector sz),
    popout (Vector.shiftin x xs) = (xs,x).
Proof.
  intros sz x xs.
  induct_on_vec xs.
Qed.


Lemma rotMSB_S_n : forall n v, rotTowardsMSB (S n) v = let (xs,x) := popout v in (x :: xs).
Proof.
  intros.
  crush.
Qed.

Lemma rotMSB_LSB_inv : forall sz (v : Bvector sz),
    rotTowardsMSB sz (rotTowardsLSB sz v) = v.
Proof.
  Hint Rewrite rotMSB_S_n popout_shiftin :bitvector.
  Hint Unfold rotTowardsLSB : bitvector.
  intros sz v.
  destruct v; crush.
Qed.

Lemma BVrotL1 : forall sz n (v : Bvector sz), BVrotL 1 (BVrotR (S n) v) = BVrotR n v.
Proof.
  intros. simpl.
  rewrite rotMSB_LSB_inv.
  trivial.
Qed.

Lemma BVrotRL_inv : forall sz n (v : Bvector sz), BVrotL n (BVrotR n v) = v.
Proof.
  intros sz n v.
  induction n; trivial.
  rewrite <- Nat.add_1_r.
  rewrite <- BVrotL_add.
  rewrite Nat.add_1_r.
  rewrite BVrotL1.
  assumption.
Qed.


(** injectivity of Bv2N function *)

Lemma inj : forall sz (v0 v1 : Bvector sz),  Bv2N v0 = Bv2N v1 -> v0 = v1.
Proof.
  intros sz v0 v1.
  intros pfBv2NEq.
  pose (f_equal (N2Bv_sized sz) pfBv2NEq) as Hyp.
  repeat rewrite N2Bv_sized_Bv2N in Hyp.
  trivial.
Qed.

(* begin hide *)

Module ArithmInternals.
  (**
      ShiftR and division.
   *)
  Lemma shiftin_cons : forall sz b0 b1 (vec : Bvector sz),
    Vector.tl (Vector.shiftin b0 (b1 :: vec)) = Vector.shiftin b0 vec.
  Proof.
    intros. induct_on sz.
  Qed.

  Lemma shiftin_false : forall sz (vec : Bvector sz),
      @Bv2N _ (Vector.shiftin false vec) = @Bv2N _ vec.
  Proof.
    intros sz vec. induct_on sz.
  Qed.

  Hint Rewrite shiftin_false : bitvector.


  Lemma Bv2N_shiftR_1 : forall sz b (vec : Bvector sz),
      Bv2N (BVshiftR1 (b :: vec)) = Bv2N vec.
  Proof.
    intros sz b vec.
    induct_on vec.
  Qed.

  Hint Rewrite Bv2N_shiftR_1 : bitvector.


  Lemma Bv2N_shiftR_1_div : forall sz (vec : Bvector sz), Bv2N (BVshiftR1 vec) = N.div2 (Bv2N vec).
  Proof.
    intros sz vec.
    Hint Rewrite shiftin_cons shiftin_false N.div2_double Ndouble_twice : bitvector.
    unfold BVshiftR1.
    unfold BshiftRl; unfold Bhigh;
      induction vec; crush.
  Qed.

  Hint Rewrite Bv2N_shiftR_1_div : bitvector.

  Lemma inj_shiftR : forall sz n (vec : Bvector sz),
      Bv2N (BVshiftR n vec) = N.shiftr (Bv2N vec) (N.of_nat n).
  Proof.
    intros sz n vec.
    unfold BVshiftR.
    Hint Rewrite N.shiftr_succ_r : bitvector.
    induction n; crush.
    NFacts.crush.
  Qed.

  Lemma N2Bv_sized_0 : forall x, N2Bv_sized 0 x = [].
  Proof.
    now (intros; destruct x; compute).
  Qed.


  Lemma N2Bv_sized_succ : forall sz x, N2Bv_sized (S sz) x = N.odd x  :: (N2Bv_sized sz (N.div2 x)).
  Proof.
    intros sz x.
    destruct x as [|pos]. simpl; f_equal.
    destruct pos;  simpl; f_equal.
  Qed.


  Lemma Bv2N_cons : forall sz b (vec : Bvector sz), Bv2N  (b :: vec) = ((N.b2n b) + 2 * Bv2N vec)%N.
  Proof.
    intros sz b vec.
    simpl.
    destruct b.
    destruct (Bv2N vec); trivial.
    destruct (Bv2N vec); trivial.
  Qed.

  Lemma Bv2N_false : forall m, Bv2N (Bvect_false m) = 0%N.
  Proof.
    intro m.
    induct_on m.
  Qed.

  Lemma Nb2n_mod : forall x, (N.b2n(N.odd x) = x mod 2)%N.
  Proof.
    intro x.
    rewrite <- N.bit0_mod.
    f_equal.
    auto using N.bit0_odd.
  Qed.

  Lemma Bv2N_N2Bv_sized_mod  : forall sz x, Bv2N (N2Bv_sized sz x) = (x mod 2^N.of_nat sz)%N.
  Proof.
    Hint Rewrite
         N2Bv_sized_0 N2Bv_sized_succ
         N.mod_1_r Bv2N_cons
         N.div2_div
         N.pow_succ_r
         N.mod_mul_r
         Nat2N.inj_succ
    : bitvector.

    Hint Resolve Nb2n_mod N.le_0_l : bitvector.
    intro sz.
    induction sz as [|n IHsz]. intro x; crush.
    intro x; autorewrite with bitvector; try (rewrite IHsz; rewrite N.add_cancel_r); crush.

  Qed.

  Lemma Bv2N_N2Bv_sized  : forall sz x, N.size_nat x <= sz -> Bv2N (N2Bv_sized sz x) = x.
  Proof.
    intros.
    Hint Resolve Nsize_nat_pow_2 : bitvector.
    Hint Rewrite N.mod_small     : bitvector.
    Hint Rewrite Bv2N_N2Bv_sized_mod : bitvector.
    crush.
  Qed.


  Lemma Bv2N_lt_pow_2_size : forall sz (v : Bvector sz), (Bv2N v < 2^(N.of_nat sz))%N.
  Proof.
    intros sz v.
    apply Nsize_nat_pow_2.
    (*   N.size_nat (Bv2N v) <= sz *)
    apply Bv2N_Nsize.
  Qed.
  Hint Resolve Bv2N_lt_pow_2_size : bitvector.

  Lemma Bv2N_mod_2_size  : forall sz (v : Bvector sz), (Bv2N v mod 2^(N.of_nat sz) = Bv2N v)%N.
  Proof.
    intros.
    rewrite N.mod_small; trivial.
    apply Bv2N_lt_pow_2_size.
  Qed.

  Lemma Bv2N_true : forall m : nat, Bv2N (Bvect_true m) = N.ones (N.of_nat m).
  Proof.
    intro m.
    unfold Bvect_true.
    induction m; trivial.
    simpl Vector.const.
    simpl Bv2N.
    rewrite IHm.
    rewrite Nat2N.inj_succ.
    rewrite <- N.add_1_l.
    rewrite N.ones_add.
    rewrite N.pow_1_r.
    rewrite N.succ_double_spec.
    assert (nones:N.ones 1 = 1%N) by (compute; trivial).
    rewrite nones; trivial.
  Qed.


  Lemma N_ones_size : forall n, N.size_nat (N.ones (N.of_nat n)) <= n.
    intro.
    rewrite <- Bv2N_true.
    apply Bv2N_Nsize.
  Qed.


  Lemma N_ones_size_gen : forall sz n, n <= sz -> N.size_nat (N.ones (N.of_nat n)) <= sz.
  Proof.
    Hint Resolve Nat.le_trans : bitvector.
    Hint Resolve N_ones_size : bitvector.
    intros sz n pfSzLeN.
    crush.
  Qed.

End ArithmInternals.
Import ArithmInternals.
Hint Resolve Bv2N_N2Bv_sized_mod : bitvector.

(* end hide *)

(* ** Arithmetic facts.

The connection between bitwise operation and the corresponding
arithmetic operations are proved here. The facts [Bv2N_shiftR] and
[Bv2N_selectLower] takes care of division and reminder. We also show
that addition and multiplications are equivalent to their modulo
[2^sz] counterparts.

To prove claims about overflow free computation, we have lemmas that
prove the correctness of addition when the number of bits is less than
the bitvector size.

*)

Lemma Bv2N_shiftR : forall sz n (vec : Bvector sz), Bv2N (BVshiftR n vec) = (Bv2N vec / 2^N.of_nat n)%N.
Proof.
  Hint Rewrite inj_shiftR : bitvector.
  Hint Resolve N.shiftr_div_pow2 : bitvector.
  intros sz n vec.
  crush.
Qed.


Lemma Bv2N_selectLower : forall sz n (vec : Bvector sz),
    n <= sz -> Bv2N (selectLower n vec) = (Bv2N vec mod 2^(N.of_nat n))%N.
Proof.
  intros.
  unfold selectLower.
  unfold lower_ones.
  rewrite Nand_BVand.

  Hint Resolve N_ones_size_gen N.land_ones : bitvector.
  rewrite Bv2N_N2Bv_sized; eauto with bitvector.
Qed.


Lemma Bv2N_plus_mod : forall sz (v0 v1 : Bvector sz),
    (Bv2N (BVplus v0 v1) = (Bv2N v0 + Bv2N v1) mod 2^(N.of_nat sz))%N.
Proof.
  unfold BVplus.
  intros.
  unfold arithm.
  eauto with bitvector.
Qed.

Lemma Bv2N_mul_mod : forall sz (v0 v1 : Bvector sz),
    (Bv2N (BVmul v0 v1) = (Bv2N v0 * Bv2N v1) mod 2^(N.of_nat sz))%N.
Proof.
  unfold BVmul.
  intros.
  unfold arithm.
  eauto with bitvector.
Qed.




Lemma Bv2N_plus : forall sz n (v0 v1 : Bvector sz),
    BVN_size_nat v0 <= n -> BVN_size_nat v1 <= n -> n < sz ->
    (Bv2N (BVplus v0 v1) = Bv2N v0 + Bv2N v1)%N.
Proof.
  Hint Resolve Nadd_bound_nat_gen : bitvector.
  intros.
  rewrite Bv2N_plus_mod;
  rewrite N.mod_small; trivial.
  eauto with bitvector.
Qed.


Lemma Bv2N_mul : forall sz n0 n1 (v0 v1 : Bvector sz),
     BVN_size_nat v0 <= n0 -> BVN_size_nat v1 <= n1 -> n0 + n1 <= sz ->
    (Bv2N (BVmul v0 v1) = Bv2N v0 * Bv2N v1)%N.
Proof.
  unfold BVN_size_nat.
  intros.
  rewrite Bv2N_mul_mod.

  rewrite N.mod_small; trivial.
  assert (Bv2N v0 * Bv2N v1 < 2^(N.of_nat (n0 + n1)))%N
    by now apply Nmul_bound_nat.
  eauto with Nfacts.
Qed.
