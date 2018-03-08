Require Import Verse.Word.
Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Language.Operators.
Require Import Verse.Semantics.

Module EmptyWord <: WORD_SEMANTICS.

  Definition wordDenote (n : nat) : Type := unit.

End EmptyWord.

Module EmptyConsts <: CONST_SEMANTICS EmptyWord.

  Definition constWordDenote n (w : StandardWord.wordDenote n) : EmptyWord.wordDenote n := tt.

End EmptyConsts.

Module EmptyOps <: OP_SEMANTICS (EmptyWord).

  Definition OpError := False.

  Definition wordOpDenote la ra n (o : op la ra) : arityDenote OpError la ra (EmptyWord.wordDenote n).
    destruct o; repeat constructor.
  Defined.

End EmptyOps.

Module EmptySemantics := Semantics EmptyWord EmptyConsts EmptyOps.
