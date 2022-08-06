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

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B C : v of type Word8.

  Definition f (w : VariableT) (a b : w of type Word8)
    : specBlock bvDenote w.

    verse ([code| a := b + b |]
                DOES
          (VAL a = INIT b + INIT b)
          )%list%verse.
  Defined.

  Definition verF : verFun bvDenote.
    Pack f.
    realize.
  Defined.

  Fixpoint repeat (n : nat) : list (modular bvDenote v).
    exact match n with
          | 0 => []
          | S n => ([code| B := A; A := `6` |]
                    ++
                    (ASSERT VAL B = INIT A)
                    ++
                    [ CALL verF WITH (- A, B -) ])%verse
                    ++ repeat n
          end%list.
    Defined.

  Definition test : list (modular bvDenote v).
    (* This actually works without the `verse` tactic *)
    verse (
        [code| A := A; B := B; C := `0` |]
        ++
        [ CALL verF WITH (- A, B -) ]
        ++
        repeat 1
        ++
        (ASSERT VAL A = INIT B + INIT B + INIT B + INIT B)
        ++
        (ASSERT VAL A = VAL C)
      )%list%verse.
  Defined.

End Code.

Definition toProve : Prop.
  getProp test.
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
