Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.Monoid.
Require Import Verse.ScopeStore.

Require Import Verse.
(* The file defining a custom entry seems to be a required import to
   import any file using said custom entry!

   Might have to change `Require Import Verse` and `Require Import
   Verse.Language` to `Require Export`s.
 *)
Require Import Verse.AbstractMachine.
Require Import Verse.AnnotatedCode.


Open Scope annotation_scope.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v Word8.

  Definition f (w : VariableT) (a b : w _ Word8)
    : specified bvDenote noRels w AnnotatedCode.

    verse (CODE [code| a := b + `2` |]
                DOES
           [verse| a = `OLD b` + `2` |]
          )%list%verse.
  Defined.

  Definition test : AnnotatedCode bvDenote noRels v.
    (* This actually works without the `verse` tactic *)
    verse (
        CODE [code| A := A; B := B |]
        ++
        CALL f WITH (- A, B -)
        ++
        ANNOT [code| A = `OLD B` + `2` |]
        ++
        CODE [code| B := A; A := `6` |]
        ++
        CALL f WITH (- A, B -)
        ++
        ANNOT [code| A = `OLD B` + `4` |]
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
