Require Import Verse.Word.
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

  Definition constWordDenote n (w : StandardWord.wordDenote n) : NWord.wordDenote n :=
    let 'bits wv := w in
    let len := 8 * 2^n in
    Bv2N len wv.

End NConst.

Module NOps <: OP_SEMANTICS (NWord).

  Definition OpError := True.

  Definition wordOpDenote la ra n (o : op la ra) : arityDenote OpError la ra (NWord.wordDenote n) :=
    match o in op la0 ra0 return arityDenote OpError la0 ra0 (NWord.wordDenote n) with
    | plus => fun a b => {- N.add a b -}
    | minus => fun a b => {- N.sub a b -}
    | mul => fun a b => {- N.mul a b -}
    | exmul => fun a b => (error I, error I)
    | quot => fun a b => {- N.div a b -}
    | eucl => fun a b c => (error I, error I)
    | rem => fun a b => {- N.modulo a b -}
    | bitOr => fun a b => {- N.lor a b -}
    | bitAnd => fun a b => {- N.land a b -}
    | bitXor => fun a b => {- N.lxor a b -}
    | bitComp => fun a => error I
    | rotL m => fun b => error I
    | rotR m => fun b => error I
    | shiftL m => fun b => error I
    | shiftR m => fun b => error I
    | nop => fun b => {- b -}
    end.

End NOps.

Module NSemantics := CodeSemantics NWord NConst NOps.
