(** * Type Systems.

The verse language, as well as the target languages, are expected to
be typed. Types themselves are distinguished by [kind]; types of the
[direct] [kind] capture types that can be held in machine registers
where as that of [memory] [kind] are stored in the memory. Arrays
types are examples of types of the [memory] kind. In addition, arrays
also have endianness encoded.

Target languages might choose to ignore some aspects, like for example
arrays do not carry a notion of endianness in C, but the translation
process from verse to the target language is expected to take care of
these. One can view this as a erasure of some of the typing
information as we compile to a lower level target language.

*)

Inductive kind   : Set := direct | memory.
Inductive endian : Set := bigE | littleE | hostE.

Structure typeSystem :=
  TypeSystem { typeOf       :> kind -> Type;
               arrayType    : nat -> endian -> typeOf direct -> typeOf memory;
               constOf      : typeOf direct -> Type;
               (* TODO: const and operators can be combined where constants are just 0 arity operators *)
               operator     : typeOf direct -> nat -> Type
             }.
(** A type existentially quantified by its kind. Such existentlly quantified types
    makes it possible to store types of different kind in a list or a vector
*)
Definition some := @sigT kind.

(** * Translator and compilers.

A translator between type systems is mapping between their types
together with a type preserving mapping of constants. A compiler is a
translator which can err --- in general not all types in the source
type system have faithful representation in the target type system.
For a target type system [tgt], we define [result tgt] such that a
compiler from a source type system [src] to [tgt] is just a translator
form [src] to [result tgt].

*)

Structure translator (ts0 ts1 : typeSystem)
  := TypeTranslation
       {
         typeTrans   :> forall {k : kind}, ts0 k -> ts1 k;
         constTrans  : forall ty : ts0 direct,
             constOf ts0 ty -> constOf ts1 (typeTrans ty);
         opTrans     : forall (ty : ts0 direct) arity,
             operator ts0 ty arity -> operator ts1 (typeTrans ty) arity;
         arrayCompatibility : forall b e ty,
             typeTrans (arrayType ts0 b e ty) = arrayType ts1 b e (typeTrans ty)
       }.

(* begin hide *)
Arguments TypeTranslation [ts0 ts1].
Arguments typeTrans [ts0 ts1] _ [k].
Arguments constTrans [ts0 ts1] _ [ty].
Arguments arrayCompatibility [ts0 ts1].
Arguments opTrans [ts0 ts1] _ [ty arity].
Require Import Verse.Error.

(* end hide *)

Definition same ts : translator ts ts
  := {| typeTrans  := fun _ => id;
        constTrans := fun _ => id;
        opTrans    := fun _ _ => id;
        arrayCompatibility := fun _ _ _ => eq_refl
     |}.

Definition result (tgt : typeSystem) :=
  let resultType tgt k := typeOf tgt k + {TranslationError} in
  let resultArray tgt b e : resultType tgt direct -> resultType tgt memory
      := fmap (arrayType tgt b e) in
  let resultConst tgt  (ty : resultType tgt direct) :=
      match ty with
      | {- tyC -} => constOf tgt tyC
      | _         => Empty_set + {TranslationError}
      end in
  let resultOp tgt (ty : resultType tgt direct) n :=
      match ty with
      | {- tyC -} => operator tgt tyC n
      | _         =>  Empty_set + {TranslationError}
      end in
  TypeSystem (resultType tgt) (resultArray tgt) (resultConst tgt) (resultOp tgt).

Definition compiler src tgt := translator src (result tgt).

(**

An injector is a special compiler from a type system to itself which
just injects the type into the result type system.

 *)

Definition injector ts : compiler ts ts :=
  {| typeTrans := fun k ty => (fun t : typeOf (result ts) k => t) {- ty -};
     constTrans := fun _ c => c ;
     opTrans    := fun _ _ o => o;
     arrayCompatibility := fun _ _ _ => eq_refl
  |}.

(**

Our semantics machine needs to be executed in Coq and hence the
machine types are types in Coq. We therefore have the following type
system.

*)


(** The universe of  n-ary operator on a type T *)
Fixpoint nary T (n : nat):=
  match n with
  | 0   => T
  | S m => T -> nary T m
  end.

Definition abstract_type_system : typeSystem
  := {| typeOf    := fun k => Type;
        arrayType := fun n _ ty =>  Vector.t  ty n;
        constOf   := fun ty => ty;
        operator  := nary
     |}.

Definition typeDenote ts := TypeSystem.translator ts abstract_type_system.


(** ** Translating/compiling under type translation/compilation

Giving a type translator/compiler is the first step towards eventual
translation/compilation of verse programs to executable code. The
[typeSystem] translator/compiler, can often be lifted to compile
various [typeSystem] parameterised objects. The naming convention we
follow for these lifted functions are:

1. The function [translate] takes a [typeSystem] [translator] and
   lifts it to a translation of the object in question.

2. The function [compile] is like translate but takes a type
   [compiler] instead. Also the result of the compilation is captured
   by the [result] type.

3. In some cases, the translation/compilation is contra-variant, in
   the sense that they give a map from the target object to the source
   object (with errors handled appropriately). In such cases, we call
   them coTranslate and coCompile respectively and instead of the
   result type, we will have the input type.

4. The inject/coInject are the compilation/coCompilation using the
   [injector] compiler. In some cases, they may both exist.

To avoid name conflicts, we package the translate/compile functions of
each objects into its own separate modules. The functions are expected
to be used qualified.

*)


(** *** The translate/compile/result functions for types. *)
Require Import Basics.

Module Types.

  (** The universe of types *)
  Definition U := kind -> Set.

  Definition translate src tgt (tr : translator src tgt) k (ty : typeOf src k)
    : tgt k := tr k ty.

  Arguments translate [src tgt] tr [k].

  Definition inject ts : forall k, typeOf ts k -> typeOf (result ts) k
    := translate (injector ts).

  Arguments inject [ts k].

  Definition compose {ts0 ts1 ts2}
                     (tr2 : translator ts1 ts2)
                     (tr1 : translator ts0 ts1)
    : translator ts0 ts2
    := {|
        typeTrans  := fun k => compose (typeTrans tr2 (k := k))
                                       (typeTrans tr1 (k := k));
        constTrans := fun ty => compose (constTrans tr2 (ty := typeTrans tr1 ty))
                                        (constTrans tr1 (ty := ty));
        opTrans    := fun ty n => compose (opTrans tr2 (arity := n))
                                          (opTrans tr1 (arity := n));
        arrayCompatibility := fun b e ty => eq_trans (f_equal _ (arrayCompatibility tr1 b e _))
                                                     (arrayCompatibility tr2 b e (typeTrans tr1 ty))
      |}.

  Definition compile src tgt (cr : compiler src tgt) k (ty : typeOf src k)
    : typeOf tgt k + {TranslationError}
    := translate cr ty.

  Arguments compile [src tgt] cr [k].

  Definition result tgt := typeOf (result tgt).

  (** *** Translate/Compile for existentially quantified types. *)
  Module Some.

    Definition translate src tgt
               (tr : translator src tgt)
               (s : some (typeOf src))
    : some (typeOf tgt)
      := existT _ (projT1 s) (Types.translate tr (projT2 s)).

    Arguments translate [src tgt].

    Definition inject ts : some (typeOf ts) -> some (result ts)
      := fun x => existT _ _ {- projT2 x -}.
    Arguments inject [ts].

    Definition result tgt := some (result tgt).

    Definition compile src tgt
               (cr : compiler src tgt)
               (s : some (typeOf src))
      := translate cr s.

    Arguments compile [src tgt].
  End Some.

End Types.

(** *** Translate/result/compile for constants. *)
Module Const.

  Definition translate src tgt
             (tr : translator src tgt)
             (ty : typeOf src direct)
             (c  : constOf src ty )
  : constOf tgt (Types.translate tr ty)
    := constTrans tr c.

  Arguments translate [src tgt] tr [ty].

  Definition inject ts : forall ty,
       constOf ts ty -> constOf (result ts) (Types.inject ty)
    := translate (injector ts).

  (** Constants have a default co-injection **)
  Definition coInject ts : forall ty, constOf (result ts) (Types.inject ty) -> constOf ts ty
    := fun ty => fun X => X.

  Arguments inject [ts ty].
  Arguments coInject [ts ty].

  Lemma injection_lemma : forall ts ty (c : constOf ts ty), c = coInject (inject c).
  Proof.
    trivial.
  Qed.

  Definition result tgt (ty  : Types.result tgt direct) :=
    match ty with
    | {- good -} => constOf tgt good
    | error trE  => Empty_set + {TranslationError}
    end.

  Arguments result [tgt].
  Definition compile src tgt
             (cr : compiler src tgt)
             (ty : typeOf src direct)
             (c  : constOf src ty)
    : result (Types.compile cr ty)
    := constTrans cr c.

  Arguments compile [src tgt] cr [ty].

End Const.


(**
This module captures variables used in verse programs.

 *)

Import EqNotations.

Module Variables.

  (** The universe of variables (of a given type system) *)
  Definition U ts := sigT (typeOf ts) -> Type.

  Definition renaming {ts} (u v : U ts) := forall ty,  u ty -> v ty.

  Module Universe.

    Definition coTranslate src tgt
               (tr : translator src tgt)
               (v : U tgt) : U src
      := fun ty => v (Types.Some.translate tr ty).

    Arguments coTranslate [src tgt] tr.

    Inductive translate {src tgt}
               (tr : translator src tgt)
               (v : U src) : U tgt
      := push ty : v ty -> translate tr v (Types.Some.translate tr ty).

    (** Translation of the variable universe is contravariant and
        hence the injector naturally gives a coInject instead of
        an inject. However, like in the case of constants, we can
        define an injection explicityly and we have an injection_lemma
        as a result.
     *)
    Definition coInject ts : U (result ts) -> U ts := coTranslate (injector ts).

    Definition inject   ts : U ts  -> U (result ts)
      := fun v ty => match ty with
                     | existT _ _ {- good -} => v (existT _ _ good)
                     | existT _ _ (error _)  => Empty_set
                  end.

    Arguments coInject [ts].
    Arguments inject   [ts].

    (* The following injection_lemma might need functional
       extensionality. We instead avoid using this at its only (previous)
       call site, where a direct proof is possible.
     *)

    Lemma injection_lemma : forall ts (v : U ts), v = coInject (inject v).
    Abort.

    Definition coCompile  src tgt
               (cr : compiler src tgt)
               (v : U tgt) : U src
      := coTranslate cr (inject v).
    Arguments coCompile [src tgt].

    (*
       The use case and motivation of embed is listed in Monoid/Interface
    *)
    Definition embed ts : U ts -> U (result ts)
      := fun (v : U ts) ty
         => forall good, projT2 ty = {- good -} -> v (existT _ _ good).

    Arguments embed [ts] v ty.

  End Universe.

  Definition coTranslate src tgt
             (tr : translator src tgt)
             (v : U tgt)
             (ty : some (typeOf src))
    : v (Types.Some.translate tr ty) -> Universe.coTranslate tr v ty
    := fun x => x.

  Definition translate src tgt
             (tr : translator src tgt)
             (v : U tgt)
             (ty : some (typeOf src))
    : Universe.coTranslate tr v ty -> v (Types.Some.translate tr ty)
    := fun x => x.

  Arguments coTranslate [src tgt] tr [v ty].
  Arguments translate [src tgt] tr [v ty].

  Definition coInject ts : forall (v : U (result ts)) (ty : some (typeOf ts)),
      v (Types.Some.inject ty) -> Universe.coInject v ty
    := coTranslate (injector ts).

  Definition inject ts (v : U ts) (ty : some (typeOf ts))
          (x : v ty) : Universe.inject v (Types.Some.inject ty)
    := rew sigT_eta _ in x.

  Arguments coInject [ts v ty].
  Arguments inject   [ts v ty].

  Lemma injection_lemma : forall ts (v : U ts) (ty : some (typeOf ts)) (x : v ty),
      rew (sigT_eta ty) in x = coInject (@inject ts v ty x).
  Proof.
    trivial.
  Qed.

  Local Definition inleft_inj {A E} {a b : A}
    : ({- a -} : A + {E}) = {- b -} -> a = b
    := fun e =>
         f_equal (fun xe : A + {E} => match xe with
                                      | {- x -} => x
                                      | error e => a
                                      end) e.

  Definition embed {ts} {v : U ts} {ty : some (typeOf ts)}
    : v ty -> Universe.embed v (Types.Some.inject ty).
    (* TODO : Not sure if this can be written cleanly *)
    unfold Universe.embed.
    intros.
    injection H as goodTy.
    rewrite <- goodTy.
    simpl.
    rewrite <- sigT_eta.
    exact X.
  Defined.

  Definition input tgt
             (v : Variables.U tgt)
             (s : Types.Some.result tgt)
    := (Variables.Universe.inject v) s.

  Arguments input [tgt].

  Definition coCompile src tgt
             (cr : compiler src tgt)
             (v : Variables.U tgt)
             (s : some (typeOf src))
    : input v (Types.Some.compile cr s) -> (Variables.Universe.coCompile cr v) s
    := fun H => H.

  Arguments coCompile [src tgt] cr [v s].

  Definition kVariable (ts : typeSystem) := forall k, ts k -> Type.
  Definition sigParam [ts] (kv : kVariable ts) : U ts
    := fun T => kv _ (projT2 T).

End Variables.
