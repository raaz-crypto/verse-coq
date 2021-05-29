Require Import NArith.
Require Import Verse.BitVector.
Require Import Verse.BitVector.Facts.
Import ArithmInternals.

Hint Resolve Bv2N_lt_pow_2_size Bv2N_mod_2_size : bitvector_arithm.

(* These rewrites will take care of expressing the bitwise addition
   multiplications in terms of its modulo definitions.
 *)

Hint Rewrite Bv2N_plus_mod Bv2N_mul_mod Bv2N_N2Bv_sized_mod
  : bitvector_arithm.

(* This rewrites will take care of pushing the modulo outwards *)
Hint Rewrite
     N.add_mod_idemp_r N.add_mod_idemp_l
     N.mul_mod_idemp_l N.mul_mod_idemp_r
  : bitvector_arithm.

Ltac arithm_crush :=
    intros;
    try (apply (inj _ _ _)); (* convert v1 = v2 to Bv2N v1 = Bv2N v2 *)
    autorewrite with bitvector_arithm;  (* Simplify to modulo equation *)
    repeat match goal with
           | [ |- (_ mod _ = _ mod _)%N ] => f_equal
           | [ |- context [ (1 * ?V)%N ]] => ring_simplify (1 * ?V)
           | _ => eauto with Nfacts bitvector_arithm; idtac
    end; try ring.

Definition zero {sz} := @BVzeros sz.
Definition one  {sz} := N2Bv_sized sz 1.

Lemma Bv2N_zero_is_0 :  forall sz, Bv2N (@zero sz) = 0%N.
Proof.
  Hint Rewrite Bv2N_false : bitvector_arithm.
  unfold BVzeros; arithm_crush.
Qed.

Hint Rewrite Bv2N_zero_is_0 : bitvector_arithm.


Lemma BVadd_0_l : forall sz (v : Bvector sz), BVplus BVzeros v = v.
Proof.
  arithm_crush. autorewrite with Nrewrites. arithm_crush.
Qed.


Lemma BVadd_comm : forall sz (v1 v2 : Bvector sz), BVplus v1 v2 = BVplus v2 v1.
Proof.
  arithm_crush.
Qed.

Lemma BVadd_assoc : forall sz (v1 v2 v3 : Bvector sz),
      BVplus v1 (BVplus v2 v3) = BVplus (BVplus v1 v2) v3.
Proof.
  arithm_crush.
Qed.

Lemma BVmul_1_l : forall sz (v : Bvector (S sz)), BVmul one v = v.
  unfold one.
  arithm_crush.
  ring_simplify (1 * Bv2N v)%N.
  arithm_crush.
Qed.

Lemma BVmul_comm : forall sz (v1 v2 : Bvector sz), BVmul v1 v2 = BVmul v2 v1.
Proof.
  arithm_crush.
Qed.

Lemma BVmul_assoc : forall sz (v1 v2 v3 : Bvector sz),
    BVmul v1 (BVmul v2 v3) = BVmul (BVmul v1 v2) v3.
Proof.
    arithm_crush.
Qed.

Lemma BVdistr_l : forall sz (v1 v2 v3 : Bvector sz),
    BVmul (BVplus v1 v2) v3 = BVplus (BVmul v1 v3)  (BVmul v2 v3).
Proof.
  arithm_crush.
Qed.

Lemma BVsub_def : forall sz (v1 v2 : Bvector sz), BVminus v1 v2 = BVplus v1 (BVnegative v2).
Proof.
  unfold BVnegative.
  Hint Rewrite Bv2N_N2Bv_sized_mod N.sub_diag : bitvector_arithm.
  Hint Resolve Bv2N_lt_pow_2_size : bitvector_arithm.
  unfold BVminus.
  unfold arithm.
  arithm_crush;
    try (rewrite N.add_sub_assoc);  try apply N.lt_le_incl;
      arithm_crush.
Qed.


Lemma BVopp_def : forall sz (v : Bvector sz), BVplus v (BVnegative v) = BVzeros.
Proof.
  unfold BVnegative.
  Hint Rewrite Bv2N_N2Bv_sized_mod N.sub_diag : bitvector_arithm.
  arithm_crush.
  try (rewrite N.add_sub_assoc); try apply N.lt_le_incl;
    try (rewrite N.add_sub_swap);
    try (rewrite N.add_mod);
    try (rewrite N.mod_same);
    try autorewrite with bitvector_arithm Nfacts ;
    trivial; arithm_crush.
Qed.

Lemma BVeqb_eq : forall sz (v1 v2 : Bvector sz), (v1 =? v2)%bitvector = true -> v1 = v2.
  unfold bveq.
  unfold BVeq.
  apply VectorEq.eqb_eq.
  exact eqb_true_iff.
Qed.

Definition bit_arithm_ring sz
  : ring_theory
      zero
      one
      (@BVplus (S sz))
      (@BVmul  (S sz))
      (@BVminus (S sz))
      (@BVnegative (S sz))
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

(* TODO: Add a ring morphism from Z to the bitvector ring *)

(*
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
      (Zdigits.Z_to_two_compl sz) :=
  {| morph0 := _;
     morph1 := _;
     morph_add := _;
     morph_sub := _;
     morph_mul := _;
     morph_opp := _;
     morph_eq := _
  |}.
Obligation 1.
*)



(** Here is how you use the ring tactic with bitvector.

*)
Open Scope bitvector_scope.

Definition bvsquare {sz} (a : Bvector sz) := BVmul a a.

(**

Unfortunately this does not work as it needs a conversion to appropriate coefficient.
Definition two {sz} := N2Bv_sized sz 2.

*)

Definition two {sz} := BVplus (@one sz) one.

Section Sz.
  Variable sz : nat.
  Add Ring bitvector : (bit_arithm_ring sz).

  Lemma sqformula : forall (a b : Bvector (S sz)),
      bvsquare (BVplus a b) = BVplus (BVplus (bvsquare a)  (bvsquare b)) (BVmul two (BVmul a b)).
  Proof.
    unfold bvsquare.
    unfold two.
    intros.
    ring.
  Qed.
End Sz.
