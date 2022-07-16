Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.Monoid.
Require Import Verse.HlistMachine.

Require Import Verse.
(* The file defining a custom entry seems to be a required import to
   import any file using said custom entry!

   Might have to change `Require Import Verse` and `Require Import
   Verse.Language` to `Require Export`s.
 *)
Require Import Verse.AbstractMachine.
Require Import Verse.AnnotatedCode.
Require Import Verse.ModularCode.
Require Import Verse.ProofTac.

Import ModularCode.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v of type Word8.

  Definition f (w : VariableT) (a b : w of type Word8)
    : specBlock bvDenote w.

    verse (CODE [code| a := b + b |]
                DOES
           (VAL a = OLDVAL b + OLDVAL b)
          )%list%verse.
  Defined.

  Definition verF : verFun bvDenote.
    Pack f.
    realize.
  Defined.

  Definition test : list (modular bvDenote v).
    (* This actually works without the `verse` tactic *)
    verse (
        CODE [code| A := A; B := B |]
        ++
        [ CALL verF WITH (- A, B -) ]
        ++
        (ASSERT VAL A = OLDVAL B + OLDVAL B)
        ++
        CODE [code| B := A; A := `6` |]
        ++
        [ CALL verF WITH (- A, B -) ]
        ++
        (ASSERT VAL A = OLDVAL B + OLDVAL B + OLDVAL B + OLDVAL B)
      )%list%verse.
  Defined.

End Code.

Definition toProve : Prop.
  getProp test.
Defined.

(*Require Import CoarseMeta.*)
Require Import ProofTac.
Definition proof : toProve.

  realize.

Abort.
