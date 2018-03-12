Require Import Verse.Word.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Language.Operators.
Require Import Verse.Error.
Require Verse.Semantics.BoundedOperations.
Require Import Verse.Semantics.

Require Import Arith.
Require Import NArith.

Module BoundWord <: WORD_SEMANTICS.

  Definition wordDenote (n : nat) : Type :=
    BoundedOperations.bounds.

End BoundWord.

Module ConstBounds <: CONST_SEMANTICS BoundWord.

  Definition constWordDenote n (w : StandardWord.wordDenote n) : BoundWord.wordDenote n :=
    let 'bits wv := w in
    let len := 8 * 2^n in
    (N.to_nat (N.log2 (Bv2N len wv)), N.to_nat (N.log2 (Bv2N len wv))).

End ConstBounds.

Module BoundedOps <: OP_SEMANTICS (BoundWord).

  Definition OpError := BoundedOperations.BoundError.

  Definition wordOpDenote la ra n (o : op la ra) : arityDenote OpError la ra (BoundWord.wordDenote n) :=
    match o in op la0 ra0 return arityDenote OpError la0 ra0 (BoundWord.wordDenote n) with
    | plus => BoundedOperations.add n
    | minus => BoundedOperations.subtract n
    | mul => BoundedOperations.multiply n
    | exmul => BoundedOperations.exmultiply n
    | quot => BoundedOperations.divide n
    | eucl => BoundedOperations.quotrem n
    | rem => BoundedOperations.remainder n
    | bitOr => BoundedOperations.bitOr n
    | bitAnd => BoundedOperations.bitAnd n
    | bitXor => BoundedOperations.bitXor n
    | bitComp => BoundedOperations.bitComp n
    | rotL m => fun b => BoundedOperations.rotL n b m
    | rotR m => fun b => BoundedOperations.rotR n b m
    | shiftL m => fun b => BoundedOperations.shiftL n b m
    | shiftR m => fun b => BoundedOperations.shiftR n b m
    | nop => fun b => {- b -}
    end.

End BoundedOps.

Module BoundSemantics := CodeSemantics BoundWord ConstBounds BoundedOps.
