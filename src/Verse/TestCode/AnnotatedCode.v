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

  Definition test : AnnotatedCode v bvDenote noRels.
    verse (
          CODE [ A ::= B;
                 B ::= 5
               ]
          ++
          ANNOT [ A = (OLD B) ]
          ++
          CODE [ B ::= A; A ::= 6 ]
          ++
          ANNOT [ B = (OLD B) ]
      )%list%verse.
  Defined.

End Code.

Definition toProve : Prop.
  getProp test.
Defined.

Definition proof : toProve.

  simplify.

Abort.
