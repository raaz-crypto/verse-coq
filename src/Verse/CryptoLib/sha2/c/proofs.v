Require Import Verse.
Require Import Verse.CryptoLib.sha2.
Require Import Verse.CryptoLib.sha2.c.portable.

Require Import Semantics.

Import StandardTactics.
Require Import WordFacts.
Require Import WordRing.

Open Scope word_scope.

Require Import Ring.
Import Nat.

Module SHAProofs (C : CONFIG).

  Import C.
  Module SHA := SHA2 C.
  Import SHA.

    (* Write a scoped version of STEP *)
  Definition scSTEP v t tp temp a b c d e f g h m k
    := STEP v t tp temp {| A := a; B := b; C := c; D := d; E := e; F := f; G := g; H := h |} m k.

  (* Extract the proof obligation from scSTEP *)
  Definition toProve : Prop.
    exParamProp scSTEP.
  Defined.

  (* A lemma for correctness of the Sigma optimization *)
  Lemma SigmaCorrect r0 r1 r2 (incr : r0 <= r1 <= r2) (w : typeDenote Word : Type)
    : RotRW r0 (XorW (RotRW (r1 - r0) (XorW (RotRW (r2 - r1) w) w)) w) =
      XorW (XorW (RotRW r2 w) (RotRW r1 w)) (RotRW r0 w).
  Proof.
    repeat rewrite rotRDistrXor;
      repeat rewrite rotRCompose;
      repeat rewrite Minus.le_plus_minus_r;
      easy.
  Qed.

  Definition proof : toProve.
    simplify.
    (* Sigma *)
    apply SigmaCorrect. apply increasing_R's.
    (* Sigma *)
    apply SigmaCorrect. apply increasing_R's.
    (* Maj *)
    rewrite AndComm.
    now rewrite AndDistrOr.
    (* Ring *)
    rewrite H3.
    Add Ring Here : (mod_semi_ring (4 * (2 * (2 ^ WordSize)))).
    now ring_simplify.

    rewrite H3.
    rewrite H2.
    rewrite H1.
    now ring_simplify.
  Qed.

End SHAProofs.
