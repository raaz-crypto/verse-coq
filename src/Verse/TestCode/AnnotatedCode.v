Require Import Verse.BitVector.
Require Import Verse.Monoid.
Require Import Verse.Machine.BitVector.
Require Import Verse.

Require Import Verse.AbstractMachine.
Require Import Verse.AnnotatedCode.


Open Scope annotation_scope.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v of type Word8.
  Variable C   : v of type Word16.

  Definition test : AnnotatedCode bvDenote noRels v.
    verse (
          CODE [code| A := B;
                      B := `5`;
                      C := `8`
               |]
          ++
          ANNOT [code| A = `OLD B` |]
          ++
          CODE [code| B := A; A := `6` |]
          ++
          ANNOT [code| B = `OLD B` |]
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
