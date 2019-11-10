(** * Type Systems.

The verse language, as well as the target systems, are expected to be
typed. Types themselves are distinguished by [kind]; types of the
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
  TypeSystem { typeOf       : kind -> Set;
               arrayType    : nat -> endian -> typeOf direct -> typeOf memory;
               constOf      : typeOf direct -> Type;
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
         typeTrans   : forall k, typeOf ts0 k -> typeOf ts1 k;
         constTrans  : forall ty : typeOf ts0 direct,
             constOf ts0 ty -> constOf ts1 (typeTrans direct ty);
         arrayCompatibility : forall b e ty,
             typeTrans memory (arrayType ts0 b e ty) = arrayType ts1 b e (typeTrans direct ty)
       }.

(* begin hide *)
Arguments TypeTranslation [ts0 ts1].
Arguments typeTrans [ts0 ts1] _ [k].
Arguments constTrans [ts0 ts1] _ [ty].
Arguments arrayCompatibility [ts0 ts1].
Require Import Verse.Error.

(* end hide *)

Definition result tgt :=
  let resultType tgt k := typeOf tgt k + {TranslationError} in
  let resultArray tgt b e : resultType tgt direct -> resultType tgt memory
      := ap (arrayType tgt b e) in
  let resultConst tgt  (ty : resultType tgt direct) :=
      match ty with
      | {- tyC -} => constOf tgt tyC
      | _         => Empty_set + {TranslationError}
      end in

  TypeSystem (resultType tgt) (resultArray tgt) (resultConst tgt).

Definition compiler src tgt := translator src (result tgt).


(** ** Translating/compiling under type translation/compilation

Giving a type translator/compiler is the first step towards eventual
translation/compilation of verse programs to executable code. The
[typeSystem] tranlator/compiler, can often be lifted to compile
various [typeSystem] parameterised objects. The naming convention we
follow for these lifted functions are:

1. The function [translate] takes a [typeSystem] [translator] and
   lifts it to a translation of the object in question.


2. The function [compile] is like translate but takes a type
   [compiler] instead.

2. The [result] type captures the result of a compiling an
   object. Recall that compilation of types can result in error and we
   need to handle these errors.

To avoid name conflicts, we package the translate/compile/result
functions of each objects into its own separate modules. The functions
are expected to be used qualified.
*)

(** *** The translate/compile/result functions for types. *)
Module Types.

  (** The universe of types *)
  Definition U := kind -> Set.

  Definition translate src tgt (tr : translator src tgt) k (ty : typeOf src k)
  : typeOf tgt k := typeTrans tr ty.

  Arguments translate [src tgt] tr [k].

  Definition compile src tgt (cr : compiler src tgt) k (ty : typeOf src k)
    := translate cr ty.

  Arguments compile [src tgt] cr [k].

  Definition result tgt := fun k => typeOf tgt k + {TranslationError}.

  (** *** Translate/Compile for existentially quantified types. *)
  Module Some.

    Definition translate src tgt
               (tr : translator src tgt)
               (s : some (typeOf src))
    : some (typeOf tgt)
      := existT _ (projT1 s) (Types.translate tr (projT2 s)).

    Arguments translate [src tgt].

    Definition result tgt := some (result tgt).

    Definition compile src tgt
               (cr : compiler src tgt)
               (s : some (typeOf src))
      : result tgt
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
Module Variables.

  (** The universe of variables (of a given type system) *)
  Definition U ts := forall k, typeOf ts k -> Set.

  (* Namespacing it so that can be used by the qualified module *)

  Definition translate src tgt
             (tr : translator src tgt)
             (v : U tgt) : U src
    := fun k ty => v k (Types.translate tr ty).

  Arguments translate [src tgt] tr.
  Definition result tgt (v : U tgt) : U (result tgt)
    := fun k ty => match ty with
                   | {- good -} => v k good
                   | error _    => Empty_set
                   end.

  Arguments result [tgt].

  Definition compile  src tgt
             (cr : compiler src tgt)
             (v : U tgt) : U src
    := translate cr (result v).


  Arguments compile [src tgt].
End Variables.


(** ** Qualified variables.

This module capture variables qualified by their types (which
themselves are existentially qualified by their kinds).

*)
Definition qualified ts (v : Variables.U ts) (s : some (typeOf ts))
  := v (projT1 s) (projT2 s).

Arguments qualified [ts].

Module Qualified.

  Definition translate src tgt
             (tr : translator src tgt)
             (v : Variables.U tgt)
             (s : some (typeOf src))
  : qualified v (Types.Some.translate tr s) -> qualified (Variables.translate tr v) s
    := fun H => H.


  Arguments translate [src tgt] tr [v s].

  Definition result tgt
             (v : Variables.U tgt)
             (s : Types.Some.result tgt)
    := qualified (Variables.result v) s.

  Arguments result [tgt].

  Definition compile src tgt
             (cr : compiler src tgt)
             (v : Variables.U tgt)
             (s : some (typeOf src))
    : result v (Types.Some.compile cr s) -> qualified (Variables.compile cr v) s
    := fun H => H.

  Arguments compile [src tgt] cr [v s].

End Qualified.
