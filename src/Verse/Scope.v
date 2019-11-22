Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Require Vector.
Import Vector.VectorNotations.

Section Scoped.

  (** * Scopes and allocations.

  In processing verse code, we often have code fragments [C] that use
  variables [x₁,...,xₙ] which needs to be finally allocated into
  registers before code generation. A convenient representation of
  such code fragment is using a function [fun x₁ => ... fun xₙ =>
  C]. Register allocation then becomes application of this function to
  appropriate register variables. We define the type [scoped] that is
  the type of all such PHOAS style code fragments. But first, we
  parameterise over the type system and the variable type.

   *)


  Variable ts : typeSystem.
  Variable v  : Variables.U ts.

  (** A scoped code of [n] variables, which themselves have [some]
      type, are parameterised by a vector of [n] types (existentially
      quantified over their kinds). We abuse the terminology type and
      call such a vector of (existentially quantified) types as types
      (of scopes).

   *)
  Definition type n :=  Vector.t (some (typeOf ts)) n.

  (*
  Definition someVar s := qualified v s.
   *)

  Fixpoint scoped {n} (st : type n)(CODE : Type) : Type :=
    match st with
    | []      => CODE
    | s :: lt => qualified v s -> scoped lt CODE
    end.

  (** An allocation that can be used to satisfy a scoped object of
      [scopeType], [st].
   *)

  Fixpoint allocation {n} (st : type n) : Type :=
    match st with
    | [] => unit
    | (x :: xs) => qualified v x * allocation xs
    end.

  (** And such an allocation can be used to "fill" up the variables *)

  Fixpoint fill {CODE} {n} {st : type n}
  : allocation st -> scoped st CODE -> CODE :=
    match st with
    | []             => fun a x => x
    | existT _ _ _:: lt => fun a x => fill (snd a) (x (fst a))
    end.

  Definition emptyAllocation : allocation [] := tt.

  Definition uncurryScope {CODE} {n} {st : type n}
    : scoped st CODE -> allocation st -> CODE
    := fun sc al =>  fill al sc.

  Fixpoint map A B (f : A -> B) n (st : type n) : scoped st A -> scoped st B
    := match st as st0
             return scoped st0 A -> scoped st0 B with
       | [] => f
       | _ :: xs => fun sStA z => map _ _ f _ _ (sStA z)
       end.

  Fixpoint scopedAlloc {n} (st : type n) : scoped st (allocation st)
    := match st as st0
             return scoped st0 (allocation st0) with
       | [] => tt
       | _ :: xs =>
         fun z =>
           map _ _ (fun a => (z, a)) _ _  (scopedAlloc xs)
       end.

    Definition curryScope {CODE}{n}{st : type n}(f : allocation st -> CODE) : scoped st CODE
    := map _ _ f _ _ (scopedAlloc st).

End Scoped.

Arguments allocation [ts] v [n].
Arguments scoped [ts] v [n].
Arguments map [ts v A B] f [n st].
Arguments curryScope [ts v CODE n st] f.
Arguments uncurryScope [ts v CODE n st].
Print uncurryScope.
Require Import Verse.Error.

(** ** Translation/compilation for type of scopes *)

Module Types.

  Definition translate src tgt
             (tr : translator src tgt)
             (n : nat)
             (st : type src n)
  : type tgt n := Vector.map (Types.Some.translate tr) st.
  Arguments translate [src tgt] tr [n].

  Definition result tgt n
    := type (TypeSystem.result tgt) n.


  Definition compile src tgt
             (cr : compiler src tgt)
             (n : nat)
             (st : type src n)
             : result tgt n
    := translate cr st .

  Arguments compile [src tgt] cr [n].
End Types.

(** ** Translation/compilation for allocations *)
Module Allocation.

  Fixpoint translate src tgt
             (tr : translator src tgt)
             (v  : Variables.U tgt)
             (n : nat)
             (st : type src n)
  :  allocation v (Types.translate tr st) ->
     allocation (Variables.Universe.translate tr v) st
    := match st with
       | [] => fun H : unit => H
       | Vector.cons _ x n0 xs
         => fun a =>
              let (f, r) := a in (Qualified.translate tr f, translate src tgt tr v n0 xs r)
        end.

  Arguments translate [src tgt] tr [v n st].
  Definition result tgt (v  : Variables.U tgt)
             (n : nat)
             (st : type (result tgt) n)
             := allocation (Variables.Universe.result v) st.

  Arguments result [tgt] v [n] st.

  Definition compile src tgt n
             (cr : compiler src tgt)
             (v : Variables.U tgt)
             (st : type src n)
             (res : result v (Types.compile cr st))
    : allocation (Variables.Universe.compile cr v) st
    := translate cr res.

End Allocation.

Definition translate src tgt
         (tr : translator src tgt)
         (v  : Variables.U tgt)
         (n : nat)
         (CODE : Type)
         (st : type src n)
         (sCode : scoped (Variables.Universe.translate tr v) st CODE)
  : scoped v (Types.translate tr st) CODE
  := let sCodeUncurried := uncurryScope sCode in
     let resultUncurry := fun a => sCodeUncurried (Allocation.translate tr a) in
     curryScope resultUncurry.
