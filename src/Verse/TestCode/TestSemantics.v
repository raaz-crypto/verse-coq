Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.
Require Import Verse.ScopeStore.

Require Import Verse.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v Word8.

  Definition test : IntAnnotatedCode v bvDenote.
    annotated_verse
      ([
        A ::= B;
        ASSERT (VAL A = OLDVAL A);
        A ::= B;
        ASSERT (OLDVAL B = VAL A + 1);
        A ::= B
      ])%list%code.
  Defined.

End Code.

(* TODO : Prop extraction tactics need to be readded for old
          AnnotatedCode. The name IntAnnotatedCode also needs
          change.
 *)
(*
Definition toProve : Prop.
  getProp test.
Defined.

Definition proof : toProve.
  simplify.
Abort.
*)
