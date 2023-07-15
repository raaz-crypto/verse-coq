Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.

Require Import Verse.

Require Import Verse.Annotated.
Require Import Verse.HlistMachine.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v of type Word8.

  Definition test : Annotated.code bvDenote v.
    verse
      ([code| A := B |]
         ++
         (ASSERT VAL A = VAL B)
         ++
         [code| A := B |]
         ++
         (ASSERT INIT B = VAL A + 1)
         ++
         [code| A := B |])%list.
  Defined.

End Code.

(* TODO : Prop extraction tactics need to be readded for old
          AnnotatedCode. The name IntAnnotatedCode also needs
          change.
 *)

Definition toProve : Prop.
  vc_gen test.
Defined.

Require Import Verse.ProofTac.

Definition proof : toProve.
  realize.
Abort.
