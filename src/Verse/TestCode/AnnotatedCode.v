Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.

Require Import Verse.AbstractMachine.
Require Import Verse.AnnotatedCode.

Import AnnotatedCode.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v of type Word8.
  Variable C   : Vector.t (v of type (Array 1 bigE Word16)) 1.

  Definition test : lines bvDenote v.
    verse (
        CODE [code| A := B;
                    B := `5`;
                    C[0][0] := `8`
             |]
          ++
          (ASSERT VAL A = INIT B)
          ++
          CODE [code| B := A; A := `6` |]
          ++
          (ASSERT VAL B = INIT B)
      )%list%verse.
  Defined.

End Code.

Require Import Verse.Machine.BitVector.
Require Import Verse.HlistMachine.
Require Import Verse.ProofTac.

Definition toProve : Prop.
  getProp test.
Defined.

Definition proof : toProve.
  realize.
Qed.
