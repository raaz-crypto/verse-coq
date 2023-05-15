Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.

Require Import Verse.HlistMachine.
Require Import Verse.AnnotatedCode.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v of type Word8.
  Variable C   : Vector.t (v of type (Array 1 bigE Word16)) 1.

  Definition test : Repeat (line bvDenote v).
    verse (
        [code| A := B;
               B := `255`;
               C[0][0] := `8`
             |]
          ++
          (ASSERT (VAL A = (INIT B) & (VAL B)))
          ++
          [code| B := A; A := `6` |]
          ++
          (ASSERT VAL B = INIT B)
      )%list.

  Defined.

End Code.

Require Import Verse.Machine.BitVector.
Require Import Verse.HlistMachine.
Require Import Verse.ProofTac.

Require Import Scope.
Definition toProve : Prop.
  getProp test.
Defined.

Definition proof : toProve.
  realize.
Abort.
