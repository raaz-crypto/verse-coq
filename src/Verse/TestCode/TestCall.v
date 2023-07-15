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
Require Import Verse.Annotated.
Require Import Verse.Subroutine.
Require Import Verse.ProofTac.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B C : v of type Word8.

  Definition f (w : VariableT) (a b : w of type Word8)
    : subroutine bvDenote w.

    verse ([code| a := b + b |]
                DOES
          (VAL a = INIT b + INIT b)
          )%list.
  Defined.

  Definition verF : vsubroutine bvDenote.
    Pack f.
    realize.
  Defined.

  Definition middle : Subroutine.code bvDenote v.
    verse ([code| B := A; A := `6` |]
             ++
             (ASSERT VAL B = INIT A)
             ++
             CALL verF WITH (- A, B -))%list.
  Defined.

  Definition test : Repeat (Subroutine.statement bvDenote v).
    (* This actually works without the `verse` tactic *)
    verse (
        [code| A := A; B := B; C := `0` |]
        ++
        CALL verF WITH (- A, B -)
        ++
        [ repeat 2 middle ]
        ++
        (ASSERT VAL A = INIT B + INIT B + INIT B + INIT B)
        ++
        (ASSERT VAL A = VAL C)
      )%list.
  Defined.

End Code.

Definition toProve : Prop.
  vc_gen test.
Defined.

Require Import ProofTac.

Definition proof : toProve.
  time mrealize.
Abort.

(** Timing notes -
    mrealize
    repeat 5  - 21 sec  1 sec
    repeat 6  - 38 sec
    repeat 7  - 45 sec  8 sec
    repeat 8  - 75 sec  11 sec
    repeat 9  - 101 sec 13 sec
    repeat 10 - 133 sec 18 sec

    Realize
    repeat 5  - .3 sec
    repeat 13 - 81 sec
*)
