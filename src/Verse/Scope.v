(** printing x₁ %$x_1$%  #x<sub>1</sub># *)
(** printing xn %$x_n$%  #x<sub>n</sub># *)


Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Require Import List.
Import ListNotations.

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

  (* TODO: The following 'type' definition should be in its own
           module named Scope.
           That way this can be the only name that is hidden when
           importing Scope. Otherwise just to avoid having to write
           'type' in those places, every name in this file needs to
           be 'Scope.'ed
  *)

  Definition type := list (some (typeOf ts)).

  Definition const n (ty : typeOf ts direct)
    := List.repeat (existT _ _ ty) n.

  Fixpoint scoped (st : type)(CODE : Type) : Type :=
    match st with
    | []      => CODE
    | t::stl  => v t -> scoped stl CODE
    end.

  (** An allocation that can be used to satisfy a scoped object of
      [scopeType], [st].
   *)

  Fixpoint allocation (st : type) : Type :=
    match st with
    | []     => unit
    | t::stl => (v t * allocation stl)%type
    end.

  (** And such an allocation can be used to "fill" up the variables *)

  Fixpoint fill {CODE} {st : type}
  : allocation st -> scoped st CODE -> CODE :=
    match st with
    | []             => fun a x => x
    | existT _ _ _:: lt => fun a x => fill (snd a) (x (fst a))
    end.

  Definition emptyAllocation : allocation [] := tt.

  Definition uncurryScope {CODE} {st : type}
    : scoped st CODE -> allocation st -> CODE
    := fun sc al =>  fill al sc.

  Fixpoint map [A B] (f : A -> B) [st : type] : scoped st A -> scoped st B
    := match st as st0
             return scoped st0 A -> scoped st0 B with
       | []      => f
       | _ :: xs => fun sStA z => map f (sStA z)
       end.

  Fixpoint scopedAlloc (st : type) : scoped st (allocation st)
    := match st as st0
             return scoped st0 (allocation st0) with
       | [] => tt
       | _ :: xs =>
         fun z =>
           map (fun a => (z, a)) (scopedAlloc xs)
       end.

    Definition curryScope {CODE}{st : type}(f : allocation st -> CODE) : scoped st CODE
    := map f (scopedAlloc st).

End Scoped.

Arguments const [ts] n ty.
Arguments allocation [ts] v.
Arguments scoped [ts] v.
Arguments map [ts v A B] f [st].
Arguments curryScope [ts v CODE st] f.
Arguments uncurryScope [ts v CODE st].
Arguments fill [ts v CODE st].

Require Import Verse.Error.

(** ** Translation/compilation for type of scopes *)

Module Types.

  Definition translate src tgt
             (tr : translator src tgt)
             (st : type src)
  : type tgt := List.map (Types.Some.translate tr) st.
  Arguments translate [src tgt] tr.

  Definition result tgt
    := type (TypeSystem.result tgt).

  Definition inject ts := translate (TypeSystem.injector ts).

  Arguments inject [ts].

  Definition compatible  (src tgt : typeSystem)
             (cr : compiler src tgt)
             (st : type tgt) (ss : type src) : Prop
    := inject st = translate cr ss.

  Arguments compatible [src tgt] cr.

  Definition compile src tgt
             (cr : compiler src tgt)
             (ss : type src)
             : result tgt
    := translate cr ss.

  Arguments compile [src tgt] cr.

End Types.

(** ** Translation/compilation for allocations *)

Module Allocation.

  Fixpoint coTranslate src tgt
             (tr : translator src tgt)
             (v  : Variables.U tgt)
             (st : type src)
  : allocation v (Types.translate tr st) ->
    allocation (Variables.Universe.coTranslate tr v) st
    := match st with
       | []    => fun H : unit => H
       | x::xs => fun a =>
                  let (f, r) := a in
                  (Variables.coTranslate tr f, coTranslate src tgt tr v xs r)
        end.

  Fixpoint translate src tgt
           (tr : translator src tgt)
           (v  : Variables.U tgt)
           (st : type src)
    : allocation (Variables.Universe.coTranslate tr v) st
      -> allocation v (Types.translate tr st)
    := match st with
       | []    => fun H : unit => H
       | x::xs => fun a =>
                  let (f, r) := a in
                  (Variables.coTranslate tr f, translate src tgt tr v xs r)
       end.

  Arguments coTranslate [src tgt] tr [v st].
  Arguments translate   [src tgt] tr [v st].

  Definition inject ts :
    forall (v : Variables.U (result ts)) (st : type ts),
      allocation (Variables.Universe.coInject v) st ->
      allocation v (Types.inject st)
    := translate (injector ts).

  Definition coInject ts :
    forall (v : Variables.U (result ts)) (st : type ts),
      allocation v (Types.inject st) ->
      allocation (Variables.Universe.coInject v) st
     := coTranslate (injector ts).


  Arguments inject [ts v st].
  Arguments coInject [ts v st].

  Import EqNotations.

  (* We need the following lemma to define coCompile *)
  Definition list_map_tl [T U] (f : T -> U) (v : list T)
    : List.map f (List.tl v) = List.tl (List.map f v).
  Proof.
    now induction v.
  Qed.

  Section Compile.
    Variables src tgt : typeSystem.
    Variable  cr : compiler src tgt.

  Definition coCompile (st : type tgt) (ss : type src)
             (pfCompat : Types.compatible cr st ss)
             (v : Variables.U tgt)
    : allocation v st ->
      allocation (Variables.Universe.coCompile cr v) ss.
    (* In the absence of a injection_lemma for `Variables.U`, not sure
       this can be defined cleanly.
       We would have liked it to be -

         fun a => coTranslate cr (rew pfCompat in (inject a)))
     *)
    refine (fun a => coTranslate cr (rew pfCompat in (inject _))).
    revert pfCompat.
    revert ss.
    induction st.
    * intros; exact tt.
    * intros.
      unfold Types.compatible in pfCompat.
      unfold Types.inject in pfCompat.
      unfold Types.translate in pfCompat.
      pose (f_equal (@List.length _) pfCompat).
      repeat rewrite map_length in e.
      destruct ss.
      discriminate.
      constructor.
      exact (rew sigT_eta _ in fst a).
      refine (IHst (snd a) ss _).
      pose (f_equal (@List.tl _) pfCompat).
      rewrite <- list_map_tl in e0.
      exact e0.
  Defined.

  End Compile.

  Arguments coCompile [src tgt] cr [st ss] pfCompat [v] a.

End Allocation.

Definition translate src tgt
           (tr    : translator src tgt)
           (v     : Variables.U tgt)
           (ss    : type src)
           (CODE  : Type)
           (sCode : scoped (Variables.Universe.coTranslate tr v) ss CODE)
  : scoped v (Types.translate tr ss) CODE
  := let sCodeUncurried := uncurryScope sCode in
     let resultUncurry := fun a => sCodeUncurried (Allocation.coTranslate tr a) in
     curryScope resultUncurry.

Definition compile src tgt
           (cr : compiler src tgt)
           (v  : Variables.U tgt)
           (ss : type src)
           (st : type tgt)
           (pfCompat: Types.compatible cr st ss)
           (CODE : Type)
           (sCode : scoped (Variables.Universe.coCompile cr v) ss CODE)
  : scoped v st CODE
  := let sCodeUncurried := uncurryScope sCode in
     let resultUncurry := fun a => sCodeUncurried (Allocation.coCompile cr pfCompat a) in
     curryScope resultUncurry.

Arguments translate [src tgt] tr [v ss CODE].
Arguments compile   [src tgt] cr [v ss st] pfCompat [CODE].

(** ** Infering the scope type.

In verse scoped code is defined using the sectioning mechanism of
Coq. Often we would like to recover the scope type from the scoped
object. This we do by the following type class.


*)

Require Verse.Language.Types.
Class Infer t := { innerType : Type;
                   inferNesting : t ->
                                  type Types.verse_type_system
                                  *
                                  innerType
                 }.

(**

We now define a "cookedup" variable that helps us in getting hold of
the type for one level deep nesting.

*)

Module Cookup.
  Inductive var : Variables.U Types.verse_type_system :=
  | cookup : forall (ty : some Types.type), var ty.

  Definition specialise {t : Variables.U verse_type_system -> Type}
           (func : forall v, t v) :
           (t var)
  := func var.

  Fixpoint alloc (sty : type verse_type_system)
  : allocation var sty
  := match sty as sty0 return allocation var sty0 with
     | []                     => tt
     | (x :: xs) => (cookup x ,alloc xs)
     end.
End Cookup.


(** Helper type for delimiting scopes. *)
Inductive delimit A := body : A -> delimit A.
Arguments body [A].

Instance infer_delimited A : Infer (delimit A) | 0
  := {| innerType := A;
        inferNesting := fun d => let 'body i := d in ([], i)
     |}.

Instance infer_undelimited A : Infer A | 1
  := {| innerType := A;
        inferNesting := fun d => ([], d)
     |}.

Instance infer_arrow t (sub : Infer t) (ty : some Types.type)
  : Infer (Cookup.var ty -> t)
  := {| inferNesting := fun f => let '(sc, i) := inferNesting (f (Cookup.cookup ty)) in
                                 (ty :: sc, i)
     |}.

(*
Section ScopeVar.
  Variable ts : typeSystem.

  Inductive scopeVar : forall {n} (l : type ts n), Variables.U ts :=
  | headVar m (v : type ts (S m)) : scopeVar v (hd v)
  | restVar m (v : type ts (S m)) (ty : some (typeOf ts)) : scopeVar (tl v) ty
                                                         -> scopeVar v ty.

  Fixpoint mapAlloc v1 v2 (f : forall (ty : some (typeOf ts)), v1 ty -> v2 ty)
           n (l : type ts n) : allocation v1 l -> allocation v2 l :=
    match n return forall l : type ts n, allocation v1 l -> allocation v2 l with
    | S n => fun l a1 => (f _ (fst a1), mapAlloc v1 v2 f _ (tl l) (snd a1))
    | 0   => fun l _  => tt
    end l.

  (* The dummy allocation for scoped code *)
  Fixpoint scopeAlloc {n} (l : type ts n) : allocation (scopeVar l) l :=
    match n return forall l0 : type ts n, @allocation _ _ n l0 with
    | S m => fun l0 => (@headVar _ l0, mapAlloc _ _ (@restVar _ l0) _ _ (scopeAlloc (tl l0)))
    | 0   => fun _  => tt
    end l.

  (* Generic scoped code filled out with the dummy VariableT *)
  Definition fillScoped (CODE : Variables.U ts -> Type) n (l : type ts n)
             (genC : forall v, scoped v l (CODE v)) :=
    fill (scopeAlloc l) (genC (scopeVar l)).

(*
  Require Import Program.Equality.
  Definition eq_dec T := forall x y : T, x = y \/ ~ x = y.
  Definition scopeVar_eq_dec n (vT : type verse_type_system n)
    : forall {k} {ty : typeOf verse_type_system k}, eq_dec (scopeVar vT _ ty).
    unfold eq_dec.
    dependent induction x; dependent induction y;
      [left | right .. | idtac]; try congruence.
    destruct (IHx y);
      [left; congruence | right].
    contradict H;
      apply (f_equal ((fun (y : scopeVar (tl v) _ ty) (x : scopeVar v _ ty) =>
                         (match x in @scopeVar (S n0) v0 _ ty0
                                return scopeVar (tl v0) _ ty0 -> scopeVar (tl v0) _ ty0 with
                          | headVar _ _  => fun y => y
                          | restVar _ _ _ _ x' => fun _ => x'
                          end y)) x)
                     H).
  Defined.
   *)
End ScopeVar.

Notation "(--)"             := (tt).
Notation "(- x , .. , z -)" := (pair x .. (pair z tt) ..).

Arguments scopeVar [ts n].
Arguments headVar {ts m v}.
Arguments restVar [ts m v ty].
Arguments fillScoped [ts CODE n l] _.
*)
