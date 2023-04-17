(* begin hide *)
Require Import Verse.Ast.
Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Pretty.
Require Import Verse.Language.Macros.Loops.
Require Import List.
Require Import Psatz.
Require Import Arith.
Import ListNotations.

(*
Set Implicit Arguments.
Generalizable Variables All.

*)

(* end hide *)

Section ArrayUtils.

  (** ** Looping over array indices.

  A common coding pattern is where we need to perform some action on
  all the elements in an array. We now give functions and types that
  simplify such looping over all the indices of the array. Let [A] be
  an array variable, then the function [indices A] gives such a list
  in increasing order starting from 0. We can then use [foreach]
  function defined above to actually loop over these indices using the
  idiom [foreach (indices A) doSomethingWithIndex]. The net result is
  an unrolled loop that does some computation on every index of A. If
  one wants to perform such a loop in the reverse order on can use the
  function [indices_reversed] instead of [indices].

   *)


  Variable v : VariableT.
  Variable b : nat.
  Variable e : endian.
  Variable ty : type direct.

  (**
     This function returns the list of valid indices of an array
     variable. The indices are given starting from [0] to [b -
     1]. Mostly used in conjunction with [foreach].

   *)

  Definition indices (arr : v (existT _ _ (array b e ty))) := Loops.Internal.loop b.


  (** This function is similar to indices but gives the indices in the
      reverse order.  *)
  Definition indices_reversed (arr : v (existT _ _ (array b e ty))) := List.rev (indices arr).



  (** ** Indexing variables uniformly.

   Programming with arrays is convenient because it gives a uniform
   way to index elements which together with functions like [foreach],
   and [indices], gives concise representation of repetitive coding
   pattern. However, array indexing involves a memory operation which
   is much slower than using registers. A technique that is often uses
   is to "cache" the array in a set of registers [r0,r1...], and use
   this registers instead.  But now we loose the ability to index the
   elements uniformly which makes it tedious to write code that could
   otherwise be handled conveniently using macros like [foreach].

   The indexing problem is to give a uniform way to index a sequence of
   program variables [v0,v1,...] using their position in the list as the
   index. We solve this indexing problem as follows: We define the
   function [varIndex] that takes a vector of variables [v_0,v_1...] and
   returns the indexing function into the variables [v_0,...], i.e. the
   indexing function takes an index [i] and returns the [i]th variable
   [v_i].

   *)

  Definition VarIndex := forall i, i < b  -> v (existT _ _ ty).

  Definition varIndex (regs : Vector.t (v (existT _ _ ty)) b)
    : VarIndex := fun _ pf  => Vector.nth_order regs pf.

  (** One important use case for uniform indexing is the caching of
      arrays into a sequence of registers. We now give some helper
      functions that load and store arrays into their register cache.
   *)

  (** This macro loads the array to the corresponding chached
      variables *)
  Definition loadCache (arr : v (existT _ _ (array b e ty)))
    (ch : Vector.t (v (existT _ _ ty)) b) : Repeat (statement v) :=
    (foreach (indices arr)
            (fun i pf => let ix := @exist _ _ i pf in
                      [ Pretty.assignStmt (Vector.nth_order ch pf) (deref arr ix) ]) : code v
            ).

  (**

   This macro moves back the cached values to the given array. In
   essence this macro uses the move instruction on all the cached
   variables. This has the following consequence.

      1. The values stored in the cached variables are clobbered at
         the end, which and hence should not be used subsequently.

      2. This macro moves all the cached values back into their n
         respective positions in the array. If only few of the cached
         variables are updated since caching, it might be more
         efficient to just move those explicitly.

   *)

  Definition moveBackCache (arr : v (existT _ _ (array b e ty)))
    (ch : Vector.t (v (existT _ _ ty)) b)  : Repeat (statement v) :=
    (foreach (indices arr)
              (fun i pf => let ix := @exist _ _ i pf in
                           [ Pretty.moveStmt (deref arr ix) (Vector.nth_order ch pf) ])) : code v.

    (** This function is similar [moveCacheBack], except that it
       preserves the values in the cache variables. The cached
       variables can then be reused in the rest of the program.  *)

    Definition backupCache  (arr : v (existT _ _ (array  b e ty))) (ch : VarIndex) : Repeat (statement v) :=
      (foreach (indices arr)
              (fun i pf => let ix := @exist _ _ i pf in
                           let arrI := deref arr ix in
                           let chI := ch i pf in
                           [ Pretty.assignStmt arrI chI ]
              )) : code v.

End ArrayUtils.

(* begin hide *)
Arguments varIndex  [v b ty].
Arguments loadCache [v b e ty].
Arguments moveBackCache [v b e ty].
Arguments backupCache [v b e ty].
Arguments indices [v b e ty].
(* end hide *)


Section Selection.

  Variable A : Type.
  Variable b : nat.

(**

Given an input vector [inp] of length [b], and a vector of indices,
pick the corresponding elements from the input vector [inp].

*)
Definition select {n : nat}
           (inp : Vector.t A b)
           (to : Vector.t {i | i < b} n)
  : Vector.t A n
  := let mapper idx := Vector.nth_order inp (proj2_sig idx) in
     Vector.map mapper to.

End Selection.

Arguments select [A b n] _ _.


Require Vector.
Import Vector.VectorNotations.

(* Given a list [l] of nats, stick to each of them a proof that they
   are less than a bound [b] so that the resulting set are now a list
   of indices that can be used to index arrays and caches.
 *)


Fixpoint makeIndices (b n : nat)(l : Vector.t nat n)
  : Vector.t {i : nat | i < b } n + {exists i, Vector.In i l /\ ~ (i < b) }.
  Global Hint Constructors Vector.In : VectorIn.
  refine (match l with
          | []        => inleft []
          | (x :: xs)  =>
            match lt_dec x b, makeIndices _ _ xs with
            | left pf, inleft ixs  => inleft (@exist _ _ x pf :: ixs)
            | right pf, _ => inright (ex_intro _ x (conj _ pf))
            | left pf, inright err => inright _
            end
          end); eauto with VectorIn. destruct err. intuition. eauto with VectorIn.
Defined.


Require Import Verse.Error.

Definition tryMakeIndices {b n}(v : Vector.t nat n) := recover (makeIndices b n v).
Definition shuffleIndices {b}(v : Vector.t nat b) := @tryMakeIndices b b v.


(** Often we want to ensure that a give list of shuffle indices is
    a permutation. This proposition captures that property.
 *)
Definition Permutation {b}(v : Vector.t {i | i < b} b) :=
  let forgetproof ix := proj1_sig ix in
  forall n : nat, n < b -> Vector.In n (Vector.map forgetproof v).

Arguments makeIndices [b n].
Arguments tryMakeIndices [b n].

Arguments shuffleIndices [b] _.
Arguments Permutation [b] _.

(** A tactic notation for disposing permutation proofs. This would
     work only when the vector is just a vector of constants. But that
     is the kind of vectors that we mostly deal with crypto
     implementation.  *)


Global Tactic Notation "crush_permutation_obligation" integer(B) :=
      intros;
      repeat match goal with
             | [ H : _ <= _ |- _ ] => contradict H; lia
             | [ n : nat    |- _ ] => destruct n; eauto B with VectorIn
             end.
