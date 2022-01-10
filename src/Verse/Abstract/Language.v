Require Import Verse.Monoid.

(** * Abstract Types and code.

There are three important concepts of interest for us when dealing
with an abstract language --- the types of the language, the variable
universe, and finally the code. Since our languages are all embedded
in Coq, for every language L of interest, we have a Coq type [τ] that
represent the types of this language. Having fixed the types, the
variable universe for this type is just the type family [τ -> Type].
What is left is the code. In our setting, code is just a variable
parametrised monoid. We capture programs associated with a give type
[τ] by the following class.

*)

Module Code.
  Class class (type : Type) := { t : (type -> Type) -> Type;
                                 monoid_instance : forall v : type -> Type, Monoid (t v)
                               }.

End Code.


Instance code_monoid (type : Type)`{Code.class type}(v : type -> Type) : Monoid (Code.t v)
  := Code.monoid_instance v.

Definition sequence {type : Type}`{Code.class type}{v} (ps : list (Code.t v)) :  Code.t v :=
  mconcat ps.

(**

A more concrete instance of a program is when we have statements and
consider the monoid of list of statements (straight line
programs). Ideally, fixing the types should fix the underlying program
and hence we do not declare the definition below as an instance. When
program instances are being defined, we might want to use this
definition to declare an appropriate instances.

*)

Definition straight_line_program (type : Type)(stmt : (type -> Type) -> Type) : Code.class type
  :=  {| Code.t := fun v => list (stmt v);
         Code.monoid_instance := _
      |}.

(** * Translations

The next important consideration for us is translation between
programs written in different languages. We begin with a translation
between their types.

 *)



Module Translate.

  Class class (stype dtype : Type) := tr : stype -> dtype.

  Instance variable_translate stype dtype `{Translate.class stype dtype} : Translate.class (dtype -> Type)(stype -> Type)
    := fun v => fun st => v (Translate.tr st).


End Translate.


Module Type LanguageTranslate.

  Parameter stype dtype : Type.

  Declare Instance scode : Code.class stype.
  Declare Instance dcode : Code.class dtype.

  Declare Instance type_translate : Translate.class stype dtype.
  Declare Instance code_translation {v : dtype -> Type} : Translate.class (Code.t (Translate.tr v)) (Code.t v).

End LanguageTranslate.
