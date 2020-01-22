(* begin hide *)
Require Verse.Language.Ast.
Require Import Verse.Language.Ast.
Require Import List.
Require Import Omega.
Import ListNotations.

(* end hide *)


(** * Helper macros for loops.

When working with verse we often need to write repetitive coding
patterns. This section documents some helper functions to facilitate
refactoring such code.

 *)


(* begin hide *)

Module Internal.

  Definition indexSucc m (idx : {i | i < m}) : {i | i < S m} :=
    match idx with
    | exist _ x pf => exist _ x (le_S _ _ pf)
    end.

  Definition liftBound {m} : list {i | i < m} -> list {i | i < S m}
    := List.map (indexSucc m).

  Fixpoint loopReverse b : list {i | i < b}
    := match b with
       | 0   => []
       | S m => let bm1 : { i | i < S m} := exist _ m (le_n (S m))
               in  bm1 :: liftBound (loopReverse m)
       end.

  Definition loop b := List.rev (loopReverse b).

  (*  TODO: Prove the correctness of loop

      1. That the list is in increasing order
      2. That all elements < b are in the list.

   *)

End Internal.

Import Internal.

Section Loop.
  Variable A : Type.
  Variable b : nat.

  (** The [foreach] function is the most general looping function. It
      takes as input a list of loop indices and executes (in sequence)
      its body for each of these indices.
   *)

  Definition foreach (ixs : list {ix | ix < b})
             (f : forall ix, ix < b -> list A)
    := let mapper := fun ix => match ix with
                            | @exist _ _ i pf => f i pf
                            end
       in List.concat (List.map mapper ixs).


  (** The code fragment [iterate f] executes the commands [f 0, f 1,
      ... f (b - 1)] in sequence.  Note that the program variable type
      v and the bound b are both implicit argument that is infered
      from the input argument [f].
   *)

  Definition iterate   := foreach (loop b).

  (** Similar to [iterate] but does in the reverse order *)
  Definition iterate_reverse := foreach (List.rev (loop b)).

End Loop.

Arguments foreach [A b] _ _.
Arguments iterate [A b] _.
Arguments iterate_reverse [A b] _.
