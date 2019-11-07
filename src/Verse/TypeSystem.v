(** * Type Systems.

Verse has a strong type system that catch a lot of bugs at compile
time.  The targets that verse compile to is also expected to share a
few features of the verse type system. For example, it has a notion of
direct types and memory types. It has a way to build array of direct
types. Target languages might choose to ignore some aspects, like for
example arrays do not carry a notion of endianness in C, but the
translation process from verse to the target language is expected to
take care of these. One can view this as a erasure of some of the
typing information as we compile to a low level target language.

*)

Inductive kind   : Set := direct | memory.
Inductive endian : Set := bigE | littleE | hostE.

Structure typeSystem :=
  TypeSystem { typeOf       : kind -> Set;
               arrayType    : nat -> endian -> typeOf direct -> typeOf memory;
               constOf      : typeOf direct -> Type;
             }.


Definition some := @sigT kind.

(** * Type translation and compilation.

A type translation is mapping between the types of two type systems
which preserves the constants. A compilation is a translation which
can err --- it might be the case that certain types in the source type
system might not have faithful representation in the type system. We
represent type translation using the following structure.

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

(** ** Type compilation and result types.

For an arbitrary target type system [ts], type compilation into [ts]
can also be represented by the [typeTranslation] structure by first
considering the types [resultType ts] and the associated type system
[resultSystem ts]. Type compilation to [ts] can then be seen as a type
transaltion into [resultSystem ts].

*)

Require Import Verse.Error.

(* ** Translation results *)

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

Module Types.

  Definition translate src tgt (tr : translator src tgt) k (ty : typeOf src k)
  : typeOf tgt k := typeTrans tr ty.

  Arguments translate [src tgt] tr [k].

  Definition compile src tgt (cr : compiler src tgt) k (ty : typeOf src k)
    := translate cr ty.

  Arguments compile [src tgt] cr [k].

  Definition result tgt := fun k => typeOf tgt k + {TranslationError}.


End Types.

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
