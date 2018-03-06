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

Section ArrayUtils.

(** ** Array Indexing.

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



  Variable v : VariableT.
  Variable a : align.
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
  Definition indices (arr : v memory (array a b e ty)) :  list (Indices arr)
    := loopover b.

  (** This function is similar to indices but gives the indices in the
      reverse order.  *)
  Definition indices_reversed (arr : v memory (array a b e ty)) := List.rev (indices arr).


  (**
      This function allows mapping over all the input indices.

      <<
      foreach (indices A) statementsToTransformIthValue

      >>

      If you want to perform the action in the reverse order you can use the following idiom

      <<

     foreach (indices_reversed A) statementsToTransformIthValue

      >>

   *)

  Definition foreach (ixs : list {ix | ix < b})
             (f : forall ix, ix < b -> block v)
    := let mapper := fun ix => match ix with
                               | exist _ i pf => f i pf
                               end
       in List.concat (List.map mapper ixs).


  (** ** Array caching.

Array indexing involves a memory operation which is much slower than
using registers. It therefore makes sense to "cache" the array in a
set of registers and use this registers instead. However, the problem
with using a register cache is that we loose the ability to index the
elements uniformly. This makes writing code with register caches
rather tedious because it makes it difficult to use macros like
[foreach].

We solve the indexing problem as follows. We define the function
[cacheIn] that takes an array variable [arr], and an orders set of the
variables [v_0,v_1...] and returns the indexing function into the
variables [v_0,...], i.e. the indexing function takes an index [i] and
returns the [i]th variable [v_i]. We then use this indexing function
to access the cached values.


   *)

  Require Vector.

  Definition Cache (arr : v memory (array a b e ty)) := forall i, i < b  -> v direct ty.

  Definition cache (arr : v memory (array a b e ty)) (regs : Vector.t (v direct ty) b)
    : Cache arr := fun _ pf  => Vector.nth_order regs pf.



  (** This macro loads the array to the corresponding chached variables *)
  Definition loadCache (arr : v memory (array a b e ty)) (ch : Cache arr) : block v :=
    foreach (indices arr)
            (fun i pf => let ix := exist _ i pf in
                      let arrI := index arr ix in
                      let chI := var (ch i pf) in
                      [ assign (assign2 nop chI arrI) ]
            ).

  (**

      This macro moves back the cached values to the given array. In
      essence this macro uses the move instruction on all the cached
      variables. This has the following consequence.

      1. The values stored in the cached variables are clobbered at
         the end, which and hence should not be used subsequently.

      2. This macro moves all the cached values back into their
         respective positions in the array. If only few of the cached
         variables are updated since caching, it might be more
         efficient to just move those explicitly.

   *)
  Definition moveBackCache (arr : v memory (array a b e ty)) (ch : Cache arr)  : block v :=
    foreach (indices arr)
            (fun i pf => let ix := exist _ i pf in
                      [ moveTo arr ix (ch i pf) ]).

  (**
      This function is similar [moveCacheBack], except that it
      preserves the values in the cache variables. The cached
      variables can then be reused in the rest of the program.
   *)
  Definition backupCache  (arr : v memory (array a b e ty)) (ch : Cache arr) : block v :=
    foreach (indices arr)
            (fun i pf => let ix := exist _ i pf in
                      let arrI := index arr ix in
                      let chI := var (ch i pf) in
                      [ assign (assign2 nop arrI chI) ]
            ).



End ArrayUtils.

(* begin hide *)

Arguments Cache [v a b e ty]  _.
Arguments cache   [v a b e ty] _ _ _ _ .
Arguments loadCache [v a b e ty] _ _.
Arguments moveBackCache [v a b e ty] _ _.
Arguments backupCache [v a b e ty] _ _.
Arguments indices [v a b e ty] _.
Arguments foreach [v b] _.

(* end hide *)
