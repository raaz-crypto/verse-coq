Require Import Verse.Word.
Require Import Verse.NFacts.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Language.Operators.
Require Import Verse.Error.
Require Import Verse.Semantics.

Require Import Arith.
Require Import NArith.

Module NWord <: WORD_SEMANTICS.

  Definition wordDenote (n : nat) : Type :=
    N.

End NWord.

Module NConst <: CONST_SEMANTICS NWord.

  Definition constWordDenote n (w : constant (word n)) : NWord.wordDenote n :=
    Nibble.toN w.

End NConst.

Module NOps <: OP_SEMANTICS (NWord).

  Definition OpError := True.

  Definition wordOpDenote la ra n (o : op la ra) : arityDenote la ra (NWord.wordDenote n) :=
    let split2 n0 := (n0 / 2 ^ N.of_nat n, n0 mod (2 ^ N.of_nat n))%N in
    let merge2 n0 n1 := (2 ^ N.of_nat n * n0 + n1)%N in
    match o in op la0 ra0 return arityDenote la0 ra0 (NWord.wordDenote n) with
    | plus => fun a b => N.add a b
    | minus => fun a b => N.sub a b
    | mul => fun a b => N.mul a b
    | exmul => fun a b => split2 (a * b)%N
    | quot => fun a b => N.div a b
    | eucl => fun a b c => N.div_eucl (merge2 a b) c
    | rem => fun a b => N.modulo a b
    | bitOr => fun a b => N.lor a b
    | bitAnd => fun a b => N.land a b
    | bitXor => fun a b => N.lxor a b
    | bitComp => fun a => Bv2N n (Bvector.Bneg n (N2Bv_gen n a) )
    | rotL m => fun b => Bv2N n (BOps.BRotL m (N2Bv_gen n b))
    | rotR m => fun b => Bv2N n (BOps.BRotR m (N2Bv_gen n b))
    | shiftL m => fun b => (N.shiftl_nat b m mod two_power_nat_N (8 * 2 ^ n))%N
    | shiftR m => fun b => N.shiftr_nat b m
    | nop => fun b => b
    end.

End NOps.

Module NSemantics := Semantics NWord NConst NOps.
Module NSemanticsTactics := SemanticTactics NWord NConst NOps.
