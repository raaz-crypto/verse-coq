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

Module EmptyOps <: NoOP_SEMANTICS (EmptyWord).

  Definition wordOpDenote la ra n (o : op la ra) : ArityDenote la ra (EmptyWord.wordDenote n).
    refine
    match o with
    | plus         => _
    | minus        => _
    | mul          => _
    | exmul        => _
    | quot         => _
    | eucl         => _
    | rem          => _
    | bitOr        => _
    | bitAnd       => _
    | bitXor       => _
    | bitComp      => _
    | rotL    m    => _
    | rotR    m    => _
    | shiftL  m    => _
    | shiftR  m    => _
    | nop          => _
    end.
    all: repeat constructor.    (* there is a unique element of all function types *)
  Defined.

End EmptyOps.

Module EmptyOpSemantics := LiftOpSemantics EmptyWord EmptyOps.

Module EmptySemantics := Semantics EmptyWord EmptyConsts EmptyOpSemantics.