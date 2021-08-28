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
    : specified bvDenote noRels w AnnotatedCode.

    verse (CODE [ a ::= b + 2 ]
                DOES
           (a = OLD b + 2)
          )%list%verse.
  Defined.

  Definition test : AnnotatedCode bvDenote noRels v.
    (* This actually works without the `verse` tactic *)
    verse (
        CODE [ A ::= A; B ::= B ]
        ++
        CALL f WITH (- A, B -)
        ++
        ANNOT [ A = OLD B + 2 ]
        ++
        CODE [ B ::= A; A ::= 6 ]
        ++
        CALL f WITH (- A, B -)
        ++
        ANNOT [ A = OLD B + 4 ]
      )%list%verse.
  Defined.

End Code.

Definition toProve : Prop.
  getProp test.
Defined.

Require Import CoarseMeta.

Definition proof : toProve.

  mrealize.

Abort.
