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
Require Import Verse.Language.Types.

Structure typeSystem :=
  TypeSystem { typeOf       : kind -> Set;
               arrayType    : nat -> endian -> typeOf direct -> typeOf memory;
               constOf      : typeOf direct -> Type;
             }.


Canonical Structure verse_type_system := TypeSystem type array const.

(** ** Typed variables.

When building programming constructs, we need variables. In a typed
setting, we would like the variables to be parameterised by types. The
[VariableT ts] should be seen as the universe of program variables for
programs that use the type system [ts].

*)

Definition VariablesOf (ts : typeSystem) := forall k, typeOf ts k -> Set.
Definition VariableT := VariablesOf verse_type_system.
