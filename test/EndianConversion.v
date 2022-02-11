From Verse Require Import Verse Nibble.
Require Import Nat.
Require Import NArith.
Import VerseNotations.
Require Import String.
Open Scope string_scope.
Import List.ListNotations.

Section EndianConversion.
  Variable variable : VariableT.
  Arguments variable [k] _.
  Variable src     : variable (array 10 bigE Word16).
  Variable dest    : variable (array 10 littleE Word16).
  Definition copy i (_ : i < 10) : code variable.
    verse [code| dest[ i ] := src [ i ]  |].
  Defined.
  Definition conv := do iterate copy end.
End EndianConversion.


Require Import Verse.Target.C.

Inductive name := endian_conversion.

Definition convCE  : CodeGen.Config.programLine + {Error.TranslationError}.
  Function endian_conversion conv.
Defined.

Require Import Verse.Error.
Definition convC := recover convCE.

Compute convC.
