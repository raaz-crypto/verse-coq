Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.

Require Import Verse.

Require Import Verse.AnnotatedCode.
Require Import Verse.AbstractMachine.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Import AnnotatedCode.

Section Code.

  Variable v : VariableT.

  Variable A B : v of type Word8.

  Definition test : lines bvDenote v.
    verse
      (CODE [code| A := B |]
         ++
         (ASSERT VAL A = VAL B)
         ++
         CODE [code| A := B |]
         ++
         (ASSERT INIT B = VAL A + 1)
         ++
         CODE [code| A := B |])%list%verse.
  Defined.

End Code.

(* TODO : Prop extraction tactics need to be readded for old
          AnnotatedCode. The name IntAnnotatedCode also needs
          change.
 *)

Definition toProve : Prop.
  getProp test.
Defined.

Require Import Verse.ProofTac.

Definition proof : toProve.
  realize.
Abort.
