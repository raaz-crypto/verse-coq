Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.
Require Import Verse.ScopeStore.
Require Import Verse.AnnotatedCode.

Require Import Verse.

Open Scope annotation_scope.

Set Implicit Arguments.

 Section Code.

  Variable v : VariableT.

  Variable A B : v Word8.
  Variable C   : v Word16.

  Definition test : AnnotatedCode bvDenote noRels v.
    verse (
          CODE [code| A := B;
                      B := `5`;
                      C := `8`
               |]
          ++
          ANNOT [ A = (OLD B) ]
          ++
          CODE [code| B := A; A := `6` |]
          ++
          ANNOT [ B = (OLD B) ]
      )%list%verse.
  Defined.

End Code.

Definition toProve : Prop.
  getProp test.
Defined.

Definition proof : toProve.
  realize.
Qed.
