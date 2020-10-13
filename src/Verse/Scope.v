(** printing x₁ %$x_1$%  #x<sub>1</sub># *)
(** printing xn %$x_n$%  #x<sub>n</sub># *)


Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Require Vector.
Import Vector.VectorNotations.

Section Scoped.


  (** * Scopes and allocations.

  In processing verse code, we often have code fragments [C] that use
  variables [x₁,...,xn] which needs to be finally allocated into
  registers before code generation. A convenient representation of
  such code fragment is using a function [fun x₁ => ... fun xn =>
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
    match n as n0 return type n0 -> Type with
    | 0   => fun _  => unit
    | S m => fun v0 => (qualified v (Vector.hd v0) * allocation (Vector.tl v0))%type
    end st.
    (* This alternate definition does not interact well with certain ScopeStore

  Fixpoint allocation {n} (st : type n) : Type :=
    match st with
    | [] => unit
    | (x :: xs) => qualified v x * allocation xs
    end.

     *)
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
Arguments fill [ts v CODE n st].
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

  Definition inject ts := translate (TypeSystem.injector ts).

  Arguments inject [ts n].

  Definition compatible  (src tgt : typeSystem)
             (cr : compiler src tgt)
             (n  : nat)
             (st : type tgt n) (ss : type src n) : Prop
    := inject st = translate cr ss.

  Arguments compatible [src tgt] cr [n].

  Definition compile src tgt
             (cr : compiler src tgt)
             (n : nat)
             (ss : type src n)
             : result tgt n
    := translate cr ss.

  Arguments compile [src tgt] cr [n].

End Types.

(** ** Translation/compilation for allocations *)
Module Allocation.

  Fixpoint coTranslate src tgt
             (tr : translator src tgt)
             (v  : Variables.U tgt)
             (n : nat)
             (st : type src n)
  : allocation v (Types.translate tr st) ->
    allocation (Variables.Universe.coTranslate tr v) st
    := match st with
       | [] => fun H : unit => H
       | Vector.cons _ x n0 xs
         => fun a =>
              let (f, r) := a in (Qualified.coTranslate tr f, coTranslate src tgt tr v n0 xs r)
        end.

  Fixpoint translate src tgt
           (tr : translator src tgt)
           (v  : Variables.U tgt)
           (n : nat)
           (st : type src n)
    : allocation (Variables.Universe.coTranslate tr v) st
      -> allocation v (Types.translate tr st)
    := match st with
       | [] => fun H : unit => H
       | Vector.cons _ x n0 xs
         => fun a =>
             let (f, r) := a in (Qualified.coTranslate tr f, translate src tgt tr v n0 xs r)
       end.

  Arguments coTranslate [src tgt] tr [v n st].
  Arguments translate   [src tgt] tr [v n st].

  Definition inject ts :
    forall (v : Variables.U (result ts)) (n : nat) (st : type ts n),
      allocation (Variables.Universe.coInject v) st ->
      allocation v (Types.inject st)
    := translate (injector ts).

  Definition coInject ts :
    forall (v : Variables.U (result ts)) (n : nat) (st : type ts n),
      allocation v (Types.inject st) ->
      allocation (Variables.Universe.coInject v) st
     := coTranslate (injector ts).


  Arguments inject [ts v n st].
  Arguments coInject [ts v n st].

  Import EqNotations.

  Section Compile.
    Variables src tgt : typeSystem.
    Variable  cr : compiler src tgt.
    Variable n  : nat.

  Definition coCompile (st : type tgt n) (ss : type src n)
             (pfCompat : Types.compatible cr st ss)
             (v : Variables.U tgt)
    : allocation v st ->
      allocation (Variables.Universe.coCompile cr v) ss :=
    fun a => coTranslate cr (rew pfCompat in (inject a)).

  End Compile.

  Arguments coCompile [src tgt] cr [n st ss] pfCompat [v] a.

End Allocation.

Definition translate src tgt
           (tr    : translator src tgt)
           (v     : Variables.U tgt)
           (n     : nat)
           (ss    : type src n)
           (CODE  : Type)
           (sCode : scoped (Variables.Universe.coTranslate tr v) ss CODE)
  : scoped v (Types.translate tr ss) CODE
  := let sCodeUncurried := uncurryScope sCode in
     let resultUncurry := fun a => sCodeUncurried (Allocation.coTranslate tr a) in
     curryScope resultUncurry.

Definition compile src tgt
           (cr : compiler src tgt)
           (v  : Variables.U tgt)
           (n : nat)
           (ss : type src n)
           (st : type tgt n)
           (pfCompat: Types.compatible cr st ss)
           (CODE : Type)
           (sCode : scoped (Variables.Universe.coCompile cr v) ss CODE)
  : scoped v st CODE
  := let sCodeUncurried := uncurryScope sCode in
     let resultUncurry := fun a => sCodeUncurried (Allocation.coCompile cr pfCompat a) in
     curryScope resultUncurry.

Arguments translate [src tgt] tr [v n ss CODE].
Arguments compile   [src tgt] cr [v n ss st] pfCompat [CODE].

(** ** Infering the scope type.

In verse scoped code is defined using the sectioning mechanism of
Coq. Often we would like to recover the scope type from the scoped
object. This we do by the following type class.


*)

Require Verse.Language.Types.
Class Infer t := { nesting : nat;
                   innerType : Type;
                   inferNesting : t -> type Types.verse_type_system nesting * innerType
                 }.

(**

We now define a "cookedup" variable that helps us in getting hold of
the type for one level deep nesting.

*)

Module Cookup.
  Inductive var : Variables.U Types.verse_type_system :=
  | cookup : forall k (ty : Types.type k), var k ty.

  Definition specialise {t : Variables.U verse_type_system -> Type}
           (func : forall v, t v) :
           (t var)
  := func var.

  Fixpoint alloc {n : nat}(sty : type verse_type_system n)
  : allocation var sty
  := match sty as sty0 return allocation var sty0 with
     | []                     => tt
     | (x :: xs) => (cookup (projT1 x) (projT2 x) , alloc xs)
     end.
End Cookup.


(** Helper type for delimiting scopes. *)
Inductive delimit A := body : A -> delimit A.
Arguments body [A].

Instance infer_delimited A : Infer (delimit A) | 0
  := {| nesting := 0;
        innerType := A;
        inferNesting := fun d => let 'body i := d in ([], i)
     |}.

Instance infer_undelimited A : Infer A | 1
  := {| nesting := 0;
        innerType := A;
        inferNesting := fun d => ([], d)
     |}.

Instance infer_arrow t (sub : Infer t) k (ty : Types.type k)
  : Infer (Cookup.var k ty -> t)
  := {| nesting := S nesting;
        inferNesting := fun f => let '(sc, i) := inferNesting (f (Cookup.cookup k ty)) in
                                 (existT _ k ty :: sc, i)
     |}.
