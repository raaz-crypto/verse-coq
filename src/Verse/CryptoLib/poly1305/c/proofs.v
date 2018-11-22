Require Import Verse.
Require Import Verse.CryptoLib.poly1305.c.portable.
Require Import Semantics.NSemantics.
Import NSemanticsTactics.
Import NArith.


Definition loadClaim : Prop.
  exParamProp Internal.LOAD_COEFFICIENT.
Defined.

Require Import NFacts.

Lemma MASK26_two_pow_minus_one : Nibble.toN Internal.MASK26 = (two_power_nat_N 26 - 1)%N.
  now compute.
Qed.

Lemma MASK_masks m N : N.land N (two_power_nat_N m - 1) = (N mod two_power_nat_N m)%N.
  rewrite N.sub_1_r.
  rewrite two_power_nat_N_equiv.
  rewrite <- N.ones_equiv.
  now rewrite <- N.land_ones.
Qed.

Definition locadCorrectness : loadClaim.
  unfold loadClaim. unfold genSAT. unfold SAT. breakStore.
  lazy -[RotRW RotLW ShiftRW ShiftLW XorW AndW OrW NegW
               C.constDenote
              fromNibbles Ox
              numBinOp numUnaryOp numBigargExop numOverflowBinop
              Nat.add Nat.sub Nat.mul Nat.div Nat.pow
              N.add N.sub N.mul N.div N.div_eucl N.modulo N.pow
              N.lor N.land N.shiftr_nat N.shiftl_nat
              two_power_nat_N
              nth replace].
  repeat
    (match goal with
     | |- _ /\ _          => constructor
     | |- _ -> _          => intro
     | H : _ /\ _ |- _    => destruct H
     | H : True |- _      => clear H
     | |- True            => constructor
     | |- ?x = ?x         => trivial
     end).
  unfold C.constDenote.
  unfold NConst.constWordDenote.
  fold Internal.MASK26.
  repeat rewrite MASK26_two_pow_minus_one.
  repeat rewrite MASK_masks.
  repeat rewrite <- Nshiftr_equiv_nat.
  repeat rewrite <- Nshiftl_equiv_nat.
  simpl N.of_nat.
  repeat rewrite N.shiftr_div_pow2.
  rewrite N.shiftl_mul_pow2.
  repeat rewrite two_power_nat_N_equiv.
  simpl N.of_nat.
Abort.

Definition MulClaim : Prop.
  exParamProp Internal.MULR.
Defined.

Import Setoid.
Lemma modAddEnough a b c d n : (n <> 0 -> a mod n = c mod n -> b mod n = d mod n
                                -> (a + b) mod n = (c + d) mod n) %N.
  intros.
  rewrite N.add_mod.
  rewrite (N.add_mod c d).
  rewrite H0.
  now rewrite H1.
  all: easy.
Qed.

Lemma modMulEnough a b c d n : (n <> 0 -> a mod n = c mod n -> b mod n = d mod n
                                -> a*b mod n = c*d mod n)%N.
  intros.
  rewrite N.mul_mod.
  rewrite (N.mul_mod c d).
  rewrite H0.
  now rewrite H1.
  all: easy.
Qed.

Lemma modulusNotZero : ~ (2 ^ 130 - 5 = 0)%N.
  now compute.
Qed.

Definition MulCorrectness : MulClaim.
  unfold MulClaim.
  unfold genSAT.
  unfold SAT.
  breakStore.
  lazy -[RotRW RotLW ShiftRW ShiftLW XorW AndW OrW NegW
               C.constDenote
               fromNibbles Ox
               numBinOp numUnaryOp numBigargExop numOverflowBinop
               Nat.add Nat.sub Nat.mul Nat.div Nat.pow
               N.add N.sub N.mul N.div N.div_eucl N.modulo N.pow
               N.lor N.land N.shiftr_nat N.shiftl_nat
               nth replace].
  repeat
    (match goal with
     | |- _ /\ _          => constructor
     | |- _ -> _          => intro
     | H : _ /\ _ |- _    => destruct H
     | H : True |- _      => clear H
     | |- True            => constructor
     | |- ?x = ?x         => trivial
     end).
  cbn [C.constDenote NConst.constWordDenote].
  unfold NConst.constWordDenote.
  unfold toN.
  simpl fold_left.
  ring_simplify   ((w * w4 + w0 * w8 * 5 + w1 * w7 * 5 + w2 * w6 * 5 + w3 * w5 * 5 +
    2 ^ 26 * (w * w5 + w0 * w4 + w1 * w8 * 5 + w2 * w7 * 5 + w3 * w6 * 5) +
    2 ^ 52 * (w * w6 + w0 * w5 + w1 * w4 + w2 * w8 * 5 + w3 * w7 * 5) +
    2 ^ 78 * (w * w7 + w0 * w6 + w1 * w5 + w2 * w4 + w3 * w8 * 5) +
    2 ^ 104 * (w * w8 + w0 * w7 + w1 * w6 + w2 * w5 + w3 * w4))%N)
    ((w + 2 ^ 26 * w0 + 2 ^ 52 * w1 + 2 ^ 78 * w2 + 2 ^ 104 * w3) *
     (w4 + 2 ^ 26 * w5 + 2 ^ 52 * w6 + 2 ^ 78 * w7 + 2 ^ 104 * w8))%N.
  repeat rewrite <- N.mul_assoc.
  repeat rewrite <- N.pow_add_r.
  Opaque N.pow.
  simpl (_ ^ (_ + _))%N.
  Transparent N.pow.
  repeat rewrite <- N.add_assoc.
  repeat (apply modAddEnough; [ apply modulusNotZero | trivial | idtac ]).
  rewrite N.mul_comm.
  rewrite N.mul_assoc.
  apply modMulEnough; [ apply modulusNotZero | trivial | idtac ].
  now compute.
  all:
    rewrite N.mul_comm;
    repeat rewrite <- N.mul_assoc;
    apply modMulEnough; [ apply modulusNotZero | trivial | idtac ];
      apply modMulEnough; [ apply modulusNotZero | trivial | idtac ];
        now compute.
Qed.
