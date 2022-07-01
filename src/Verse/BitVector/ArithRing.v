Require Import NArith.
Require Import Verse.BitVector.
Require Import Verse.BitVector.Facts.
Import ArithmInternals.

Global Hint Resolve Bv2N_lt_pow_2_size Bv2N_mod_2_size : bitvector_arithm.

(* These rewrites will take care of expressing the bitwise addition
   multiplications in terms of its modulo definitions.
 *)

Hint Rewrite Bv2N_plus_mod Bv2N_mul_mod Bv2N_N2Bv_sized_mod
  : bitvector_arithm.

(* This rewrites will take care of pushing the modulo outwards *)

Hint Rewrite
     N.add_mod_idemp_r N.add_mod_idemp_l
     N.mul_mod_idemp_l N.mul_mod_idemp_r N.mod_1_l
     N.mod_same
  : bitvector_arithm.

Ltac arithm_crush :=
  intros;
  unfold one; unfold one_Bvector;
  unfold addition; unfold add_Bvector;
  unfold multiplication; unfold mul_Bvector;
  unfold subtraction; unfold sub_Bvector; unfold BVminus; unfold arithm;
  unfold opposite; unfold opp_Bvector; unfold BVnegative;
  try (apply (inj _ _ _)); (* convert v1 = v2 to Bv2N v1 = Bv2N v2 *)
  autorewrite with bitvector_arithm;  (* Simplify to modulo equation *)
    repeat match goal with
           | [ |- (_ mod _ = _ mod _)%N ] => f_equal
           | [ |- context [(?A mod _ )%N ] ] => ring_simplify (?A)
           | [ |- context [ (1 * ?V)%N ]] => ring_simplify (1 * ?V)
           | _ => eauto with Nfacts bitvector_arithm; idtac
    end; try ring.

Lemma Bv2N_zero_is_0 :  forall sz, @Bv2N sz 0  = 0%N.
Proof.
  intros.
  Hint Rewrite Bv2N_false : bitvector_arithm.
  arithm_crush.
Qed.


Hint Rewrite Bv2N_zero_is_0 : bitvector_arithm.


Lemma BVadd_0_l : forall sz (v : Bvector sz), 0 + v = v.
Proof.
  arithm_crush.
  autorewrite with Nrewrites. arithm_crush.
Qed.


Lemma BVadd_comm : forall sz (v1 v2 : Bvector sz), v1 + v2 = v2 + v1.
Proof.
  arithm_crush.
Qed.

Lemma BVadd_assoc : forall sz (v1 v2 v3 : Bvector sz),
      v1 + (v2 + v3) = (v1 + v2) + v3.
Proof.
  arithm_crush.
Qed.


Lemma Bv2N_le_2_power : forall sz (v : Bvector sz), (Bv2N v <= 2 ^ (N.of_nat sz))%N.
  intros.
  apply N.lt_le_incl.
  arithm_crush.
Qed.

Global Hint Resolve Bv2N_le_2_power : bitvector_arithm.

Lemma one_lt_2_power : forall sz, (1 < 2 ^ N.of_nat (S sz))%N.
  intros.
  rewrite Nat2N.inj_succ.
  generalize (N.of_nat sz).
  intro n;
    apply N.pow_gt_1;
    arithm_crush.
  apply N.neq_succ_0.
Qed.

Global Hint Resolve one_lt_2_power : bitvector_arithm.

Lemma Bv2N_one_is_1 : forall sz, @Bv2N (S sz) 1 = 1%N.
  intro.
  arithm_crush.
Qed.

Hint Rewrite Bv2N_one_is_1 : bitvector_arithm.

Lemma BVmul_1_l : forall sz (v : Bvector (S sz)), 1 * v = v.
  arithm_crush.
  ring_simplify (1 * Bv2N v)%N.
  arithm_crush.
Qed.

Lemma BVmul_comm : forall sz (v1 v2 : Bvector sz), v1 * v2 = v2 * v1.
Proof.
  arithm_crush.
Qed.

Lemma BVmul_assoc : forall sz (v1 v2 v3 : Bvector sz),
    v1 * (v2 * v3) = (v1 * v2) * v3.
Proof.
    arithm_crush.
Qed.

Lemma BVdistr_l : forall sz (v1 v2 v3 : Bvector sz),
    (v1 + v2) * v3 = (v1 * v3)  + (v2 *  v3).
Proof.
  arithm_crush.
Qed.

Lemma BVsub_def : forall sz (v1 v2 : Bvector sz), v1 - v2 = v1 + (- v2).
Proof.
  intros.
  Hint Rewrite Bv2N_N2Bv_sized_mod N.sub_diag : bitvector_arithm.
  Local Hint Resolve Bv2N_lt_pow_2_size : bitvector_arithm.
  arithm_crush.
  rewrite N.add_sub_assoc;
  arithm_crush.
Qed.


Lemma BVopp_def : forall sz (v : Bvector sz), v + (- v) = 0.
Proof.
  Hint Rewrite Bv2N_N2Bv_sized_mod N.sub_diag
      N.add_sub_assoc N.add_sub_swap
  : bitvector_arithm.
  arithm_crush.
Qed.

Lemma BVeqb_eq : forall sz (v1 v2 : Bvector sz), (v1 =? v2)%bitvector = true -> v1 = v2.
  unfold bveq.
  unfold BVeq.
  apply VectorEq.eqb_eq.
  exact eqb_true_iff.
Qed.


Definition bit_arithm_ring sz
  : ring_theory
      0
      1
      addition
      multiplication
      subtraction
      opposite
      (@eq (Bvector (S sz)))
  := {|
      Radd_0_l   := BVadd_0_l (S sz);
      Radd_comm   := BVadd_comm (S sz);
      Radd_assoc := BVadd_assoc (S sz);
      Rmul_1_l   := BVmul_1_l   sz;
      Rmul_comm  := BVmul_comm  (S sz);
      Rmul_assoc := BVmul_assoc (S sz);
      Rdistr_l   := BVdistr_l (S sz);
      Rsub_def   := BVsub_def (S sz);
      Ropp_def   := BVopp_def (S sz);
    |}.



(** * TODO: Add a ring morphism from Z to the bitvector ring

Require Import ZArith.
Require Zdigits.

Require ZArith.Zdigits.
Program Definition bit_arithm_morph sz
  : ring_morph
      zero one
      (@BVplus (S sz))
      (@BVmul  (S sz))
      (@BVminus (S sz))
      (@BVnegative (S sz))
      (@eq (Bvector (S sz)))
      0%Z
      1%Z
      Z.add
      Z.mul
      Z.sub
      Z.opp
      Z.eqb
      (Zdigits.Z_to_binary (S sz)) :=
  {| morph0 := _;
     morph1 := _;
     morph_add := _;
     morph_sub := _;
     morph_mul := _;
     morph_opp := _;
     morph_eq := _
  |}.


*)



(** Here is how you use the ring tactic with bitvector.

*)
Open Scope bitvector_scope.

Definition bvsquare {sz} (a : Bvector sz) := BVmul a a.

(**

Unfortunately this does not work as it needs a conversion to appropriate coefficient.
Definition two {sz} := N2Bv_sized sz 2.

*)

Require Import Verse.BitVector.

Definition sq {sz} (v : Bvector sz) := v * v.


Section Sz.
  Context (sz : nat).

  Add Ring bit_arith_ring : (bit_arithm_ring sz).

Lemma sqformula : forall  (a b : Bvector (S sz)),
    (a + b) ^ 2    = a ^ 2   +  b ^ 2 +  (1 + 1) * (a * b).
Proof.
  intros. unfold power. unfold bitvector_power_nat. unfold pow.
  ring.
Qed.


End Sz.
