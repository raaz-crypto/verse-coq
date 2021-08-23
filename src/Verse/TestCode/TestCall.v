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

  Definition f (w : VariableT) (a b : w _ Word8)
    : AnnotatedCode bvDenote noRels w.

    verse (CODE [ a ::= b
                ]
                ++
           ANNOT [ a = (OLD b) ]
          )%list%verse.
  Defined.

  Definition test : AnnotatedCode bvDenote noRels v.
    (* This actually works without the `verse` tactic *)
    verse (
        CODE [ A ::= A; B ::= B ]
             ++
        CALL f WITH (- A, B -)
             ++
        ANNOT [ A = (OLD B) ]
             ++
        CODE [ B ::= A; A ::= 6 ]
      )%list%verse.
  Defined.

End Code.

Definition toProve : Prop.
  getProp test.
Defined.

Definition proof : toProve.
  simplify.
Qed.
