Require Import Verse.Word.
Require Import Verse.NFacts.

Require Import Coq.setoid_ring.Ring_theory.
Require Import BinNums.
Require Import BinInt.

Require Import NArith.

Local Notation wO   := (bits (N2Bv_gen _ 0)).
Local Notation wI   := (bits (N2Bv_gen _ 1)).
Local Notation wadd := (numBinOp N.add).
Local Notation wmul := (numBinOp N.mul).
Local Notation weq  := (@eq (Word.t _)).

Section WordRing.

  Variable n : nat.

  Infix "==" := weq (at level 70).

  Ltac crush_mod_ring :=
    repeat (intros []); unfold numBinOp, numUnaryOp;
    apply f_equal;
    apply Bv2N_inj; rewrite ?Bv2N_N2Bv_gen_mod;
    simpl;
    try (rewrite ?N.add_mod_idemp_l);
    try rewrite ?N.add_mod_idemp_r;
    try rewrite ?N.mul_mod_idemp_l;
    try rewrite ?N.mul_mod_idemp_r;
    try rewrite N.mul_1_l;
    try rewrite N.mul_add_distr_l;
    try rewrite N.mul_add_distr_r;
    trivial;
    try rewrite N.add_assoc +
    rewrite N.mul_assoc +
    rewrite N.add_comm  +
    rewrite N.mul_comm  +
    rewrite N.mod_small;
    trivial;
    try (discriminate + apply two_power_nonzero + apply Bv2N_small).

  Lemma wadd_0_l : forall (x : Word.t n), wadd wO x == x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wadd_comm : forall (x y : Word.t n), wadd x y == wadd y x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wadd_assoc : forall (x y z : Word.t n), wadd x (wadd y z) == wadd (wadd x y) z.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wmul_1_l : forall x : Word.t n, wmul wI x == x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wmul_0_l : forall x : Word.t n, wmul wO x == wO.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wmul_comm : forall x y : Word.t n, wmul x y == wmul y x.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wmul_assoc : forall x y z : Word.t n, wmul x (wmul y z) == wmul (wmul x y) z.
  Proof.
    crush_mod_ring.
  Qed.

  Lemma wdistr_l : forall x y z : Word.t n, wmul (wadd x y) z == wadd (wmul x z) (wmul y z).
  Proof.
    crush_mod_ring.
  Qed.

  Definition mod_semi_ring : semi_ring_theory wO wI wadd wmul weq :=
    {|
      SRadd_0_l := wadd_0_l;
      SRadd_comm := wadd_comm;
      SRadd_assoc := wadd_assoc;
      SRmul_1_l := wmul_1_l;
      SRmul_0_l := wmul_0_l;
      SRmul_comm := wmul_comm;
      SRmul_assoc := wmul_assoc;
      SRdistr_l := wdistr_l
    |}.

  Add Ring Word : mod_semi_ring.

End WordRing.
