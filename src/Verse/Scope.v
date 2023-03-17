(** printing x₁ %$x_1$%  #x<sub>1</sub># *)
(** printing xn %$x_n$%  #x<sub>n</sub># *)


Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Require Import Verse.Utils.hlist.
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

  Definition scoped (st : type)(CODE : Type) : Type := curried v CODE st.

  (** An allocation that can be used to satisfy a scoped object of
      [scopeType], [st].
   *)

  Definition allocation (st : type) : Type := hlist v st.

  (** And such an allocation can be used to "fill" up the variables *)

  Definition uncurry {CODE} {st : type}
  : scoped st CODE -> allocation st -> CODE := uncurry.

  Definition curry {CODE}{st : type} : (allocation st -> CODE) -> scoped st CODE
    := curry.

End Scoped.

Arguments const [ts] n ty.
Arguments allocation [ts] v.
Arguments scoped [ts] v.
Arguments curry [ts v CODE st] f.
Arguments uncurry [ts v CODE st].

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
       | []    => fun _ => []%hlist
       | x::xs => fun a =>
                  (Variables.coTranslate tr (hlist.hd a) :: coTranslate src tgt tr v xs (hlist.tl a))%hlist
        end.

  Fixpoint translate src tgt
           (tr : translator src tgt)
           (v  : Variables.U tgt)
           (st : type src)
    : allocation (Variables.Universe.coTranslate tr v) st
      -> allocation v (Types.translate tr st)
    := match st as st0 with
       | []    => fun _ => []%hlist
       | x::xs => fun a =>
                  (Variables.translate tr (hlist.hd a) :: translate src tgt tr v xs (hlist.tl a))%hlist
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
    * intros; exact []%hlist.
    * intros.
      unfold Types.compatible in pfCompat.
      unfold Types.inject in pfCompat.
      unfold Types.translate in pfCompat.
      pose (f_equal (@List.length _) pfCompat).
      repeat rewrite map_length in e.
      destruct ss.
      discriminate.
      constructor.
      exact (rew sigT_eta _ in hlist.hd a).
      refine (IHst (hlist.tl a) ss _).
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
  := let sCodeUncurried := uncurry sCode in
     let resultUncurry := fun a => sCodeUncurried (Allocation.coTranslate tr a) in
     curry resultUncurry.

Definition compile src tgt
           (cr : compiler src tgt)
           (v  : Variables.U tgt)
           (ss : type src)
           (st : type tgt)
           (pfCompat: Types.compatible cr st ss)
           (CODE : Type)
           (sCode : scoped (Variables.Universe.coCompile cr v) ss CODE)
  : scoped v st CODE
  := let sCodeUncurried := uncurry sCode in
     let resultUncurry := fun a => sCodeUncurried (Allocation.coCompile cr pfCompat a) in
     curry resultUncurry.

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
     | []                     => []%hlist
     | (x :: xs) => (cookup x :: alloc xs)%hlist
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

Section Currying.

  Context {s : Type}.

  Fixpoint lamn n B : Type :=
    match n with
    | 0   => B
    | S n => s -> lamn n B
    end.

  Fixpoint map_lamn [n A B] (f : A -> B) : lamn n A -> lamn n B :=
    match n with
    | 0   => f
    | S n => fun la s1 => map_lamn f (la s1)
    end.

  Fixpoint curryV [n B]
    : (Vector.t s n -> B) -> lamn n B :=
    match n as n0 return (Vector.t _ n0 -> B) -> lamn n0 B with
    | 0   => fun func => func (Vector.nil _)
    | S n => fun func => fun x => curryV (fun vs : Vector.t s n => func (Vector.cons _ x _ vs))
    end.

  Class CURRY_VEC t := { curry_type : Type;
                         curry_vec  : t -> curry_type
                       }.

  Global Instance curry_undelimited B : CURRY_VEC B | 3
    := {| curry_type := B;
         curry_vec  := id
       |}.

  Global Instance curry_delimited B `{CURRY_VEC B} : CURRY_VEC (delimit B) | 2
    := {| curry_type := delimit (curry_type (t := B));
          curry_vec  := fun x => let 'body b := x in body (curry_vec b)
       |}.

  Global Instance curry_forall A (B : A -> Type) `{forall a, CURRY_VEC (B a)}
    : CURRY_VEC (forall a, B a) | 1
    := {| curry_type := forall a, curry_type (t := B a);
          curry_vec  := fun x => fun a => curry_vec (x a)
       |}.

  Global Instance curry_arrow A B `{CURRY_VEC B} : CURRY_VEC (A -> B) | 1
    := {| curry_type := A -> curry_type (t := B);
          curry_vec  := fun x => fun a => curry_vec (x a)
       |}.

  Global Instance expand_vec n B `{CURRY_VEC B}: CURRY_VEC (Vector.t s n -> B) | 0
    := {| curry_type := lamn n (curry_type (t := B));
          curry_vec  := fun x : Vector.t s n -> B => map_lamn curry_vec (curryV x)
       |}.

End Currying.

Require Import Verse.Language.Repeat.

Section Repeating.

  Class REPEAT_IN t := { repeated_type : Type;
                         repeat_in     : t -> repeated_type
                       }.

  Global Instance repeat_forall A (B : A -> Type) `{forall a, REPEAT_IN (B a)}
    : REPEAT_IN (forall a, B a) | 1
    := {| repeated_type := forall a, repeated_type (t := B a);
          repeat_in     := fun x => fun a => repeat_in (x a)
       |}.

  Global Instance repeat_arrow A B `{REPEAT_IN B} : REPEAT_IN (A -> B) | 1
    := {| repeated_type := A -> repeated_type (t := B);
          repeat_in     := fun x => fun a => repeat_in (x a)
       |}.

  Global Instance repeat_repeated B : REPEAT_IN (Repeat B) | 3
    := {| repeated_type := Repeat B;
          repeat_in     := id
       |}.

  Global Instance repeat_undelimited B : REPEAT_IN (list B) | 4
    := {| repeated_type := Repeat B;
          repeat_in     := once (A := B)
       |}.

  Global Instance repeat_delimited B `{REPEAT_IN B} : REPEAT_IN (delimit B) | 2
    := {| repeated_type := delimit (repeated_type (t := B));
          repeat_in     := fun x => let 'body b := x in body (repeat_in b)
       |}.

  Global Instance repeat_scoped ts (CODE : Variables.U ts -> Type) v sc
         `{REPEAT_IN (CODE v)}
    : REPEAT_IN (scoped v sc (CODE v))
    := {| repeated_type := scoped v sc (repeated_type (t := CODE v));
          repeat_in     := fun x => curry (repeat_in (uncurry x))
       |}.

End Repeating.
