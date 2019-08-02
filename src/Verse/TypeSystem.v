(** * Type Systems.

A generic types system for verse and its target languages. There are
two kinds of types -- direct types and the memory types. Direct types
are types whose values can reside directly in program variables (or
registers in the case of machines). Typically word types or SIMD
vector types are direct types. Memory types are those whose values are
accessed through indirect referencing. Examples for memory types are
arrays and pointers.


 *)

Inductive kind := direct | memory.

Structure typeSystem :=
  TypeSystem { type         : kind -> Set;
               const        : type direct -> Set;
               index        : type memory -> Set;
               contentType  : type memory -> type direct
             }.

(** ** Typed variables.

When building programming constructs, we need variables. In a typed
setting, we would like the variables to be parameterised by types. The
[VariableT ts] should be seen as the universe of program variables for
programs that use the type system [ts].

*)
Definition VariableT (ts : typeSystem) := forall k, forall ty : type ts k, Set.

(** ** Type systems under translation

All our languages are typed. When compiling from one language to
another, we need translations of these types. Not all types in the
source language might have meaningful translations into the target
type system in which case such translation should result in a
translation error. Given a type system [ts], we now define a type
system where the underlying types are a type of the type system [ts]
or a translation error. Such a type system can be the target of a type
translation into the language with the type system [ts].

*)
Inductive TranslationError : Prop :=
| CouldNotTranslate : forall A : Type, A -> TranslationError.

Arguments  CouldNotTranslate [A].

Section TranslatedType.
  Variable ts  : typeSystem.
  Definition transType k  := type ts k + { TranslationError }.
  Definition transConst (errType : transType direct) :=
    match errType with
    | inleft ty => const ts ty
    | inright e =>  TranslationError
    end.

  Definition transIndex (errType : transType memory) :=
    match errType with
    | inleft  ty => index ts ty
    | inright e  => TranslationError
    end.

  Definition transContentType (errType : transType memory) : transType direct :=
    match errType with
    | inleft  ty =>  inleft (contentType ts ty)
    | inright e  =>  inright e
    end.

End TranslatedType.

Canonical Structure translation_result (ts : typeSystem)
  := TypeSystem (transType ts) (transConst ts) (transIndex ts) (transContentType ts).
