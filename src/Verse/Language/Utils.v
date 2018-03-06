(* begin hide *)
Require Verse.Language.Ast.
Require Import Verse.Syntax.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.Ast.
Require Import List.
Require Import Omega.
Import ListNotations.


(* end hide *)


(** * Utility functions.

When working with verse we often need to write repetitive coding
patterns. This section documents some helper functions to facilitate
refactoring such code. Once can think of such helpers as "assembler
macros" and one of the advantage of using a DSL is that such "macros"
can be implemented in the host language; coq in this case.

 *)

(** ** Array indexing

The first set of helper functions gives convenient ways to work with
array indices. One of the most important operations is to perform
certain tasks for each element of the array. The [foreach] function
can be used for this. The first argument of the [foreach] function is
the list of indices of the array and its second argument is a function
that takes an index and generates some instructions.  Let [A] be an
array variable, then the function [indices A] gives such a list in
increasing order starting from 0.  One can think of the [foreach
(indices A) doSomethingWithIndex] as an unrolled loop that does some
computation on every index of A. If one wants to perform such a loop
in the reverse order on can use the function [indices_reversed]
instead of [indices].

*)

Section ArrayIndexing.

  Variable v   : VariableT.
  Variable b : nat.
  Variable e : endian.
  Variable ty : type direct.


  (* begin hide *)
  Local Definition ithIndex i : list { i | i < b} :=
    match lt_dec i b with
    | left pf => [exist _ i pf]
    | right _ => []
    end.


  Local Fixpoint loopover i :=
    (match i with
     | 0   => []
     | S j => loopover j
     end ++ ithIndex i)%list.

  (* end hide *)

  (**
     This function returns the list of valid indices of an array
     variable. The indices are given starting from [0] to [b -
     1]. Mostly used in conjunction with [foreach]

   *)
  Definition indices {a : align}(arr : v memory (array a b e ty)) :  list (Indices arr)
    := loopover b.

  (** This function is similar to indices but gives the indices in the
      reverse order.  *)
  Definition indices_reversed {a : align}(arr : v memory (array a b e ty)) := List.rev (indices arr).


  (**
      This function allows mapping over all the input indices.

      <<
      foreach (indices A) statementsToTransformIthValue

      >>

   *)

  Definition foreach (ixs : list {ix | ix < b})
             (f : forall ix, ix < b -> block v)
    := let mapper := fun ix => match ix with
                               | exist _ i pf => f i pf
                               end
       in List.concat (List.map mapper ixs).

End ArrayIndexing.

(* begin hide *)

Arguments indices [v b e ty] _ _.
Arguments foreach [v b] _ _.

(* end hide *)
