(** * Type Systems.

The verse language, as well as the target systems, are expected to be
typed. Types themselves are distinguished by [kind]; types of the
[direct] [kind] capture types that can be held in machine registers
where as that of [memory] [kind] are stored in the memory. Arrays are
example of memory types. In addition, arrays also have endianness
encoded.

Target languages might choose to ignore some aspects, like for example
arrays do not carry a notion of endianness in C, but the translation
process from verse to the target language is expected to take care of
these. One can view this as a erasure of some of the typing
information as we compile to a low level target language.

*)

Inductive kind   : Set := direct | memory.
Inductive endian : Set := bigE | littleE | hostE.

Structure typeSystem :=
  TypeSystem { typeOf       : kind -> Set;
               arrayType    : nat -> endian -> typeOf direct -> typeOf memory;
               constOf      : typeOf direct -> Type;
             }.

Definition some := @sigT kind.

(** * Translator and compilers.

A translator between type systems is mapping between their types
together with a type preserving mapping of constants. A compiler is a
translator which can err --- in general not all types in the source
type system might not have faithful representation in the target type
system.



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

Arguments TypeTranslation [ts0 ts1].
Arguments typeTrans [ts0 ts1] _ [k].
Arguments constTrans [ts0 ts1] _ [ty].
Arguments arrayCompatibility [ts0 ts1].

(** ** Translating/compiling under type translation/compilation


Giving a type translator/compiler is the first step towards eventual
translation/compilation of verse programs to executable code. By just
specifying the type tranlator/compiler, translation/compilation of
various [typeSystem] parameterised [Type]s can be defined. The naming
convention we follow are:

1. The function [translate] takes a [typeSystem] [translator] and
   appropriate and performs the translation for the type in question.

2. The [result] type captures the result of a compilation. Recall that
   compilation of types can result in error and we need to handle this
   error case. The result type captures such a situation.

3. The function [compile] is like translate but takes a type
   [compiler] instead. The result of a compilation is defined by the
   result type as mentioned above.

In particular, we define a [result] such that [result tgt] is the result
of compiling a typeSystem to the target type system [tgt].

*)

Require Import Verse.Error.

Definition result ts :=
  let resultType ts k := typeOf ts k + {TranslationError} in
  let resultArray ts b e : resultType ts direct -> resultType ts memory
      := ap (arrayType ts b e) in
  let resultConst ts  (ty : resultType ts direct) :=
      match ty with
      | {- tyC -} => constOf ts tyC
      | _         => Empty_set + {TranslationError}
      end in

  TypeSystem (resultType ts) (resultArray ts) (resultConst ts).

Definition compiler src ts := translator src (result ts).

(** *** The translate, compile and result for types. *)
Module Types.

  Definition translate src tgt (tr : translator src tgt) k (ty : typeOf src k)
  : typeOf tgt k := typeTrans tr ty.

  Arguments translate [src tgt] tr [k].

  Definition compile src tgt (cr : compiler src tgt) k (ty : typeOf src k)
    := translate cr ty.

  Arguments compile [src tgt] cr [k].

  Definition result tgt := fun k => typeOf tgt k + {TranslationError}.


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
