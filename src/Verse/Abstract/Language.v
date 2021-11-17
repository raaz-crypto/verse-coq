Require Import Verse.Monoid.

(** * Abstract Types and programs

There are three important concepts of interest for us when dealing
with an abstract language --- the types of the language, the variable
universe, and finally the program. Since our languages are all
embedded in Coq, for every language L of interest, we have a Coq type
[τ] that represent the types of this language. Having fixed the types,
the variable universe for this type is just the type family [τ ->
Type].  What is left is the program. In our setting programs are just
variable parametrised monoids. We capture programs associated with a
give type [τ] by the following class.

*)

Module Program.
  Class class (type : Type) := { t : (type -> Type) -> Type;
                                 monoid_instance : forall v : type -> Type, Monoid (t v)
                               }.

End Program.


Instance prog_monoid (type : Type)`{Program.class type}(v : type -> Type) : Monoid (Program.t v)
  := Program.monoid_instance v.

Definition sequence {type : Type}`{Program.class type}{v} (ps : list (Program.t v)) :  Program.t v :=
  mconcat ps.

(**

A more concrete instance of a program is when we have statements and
consider the monoid of list of statements (straight line
programs). Ideally, fixing the types should fix the underlying program
and hence we do not declare the definition below as an instance. When
program instances are being defined, we might want to use this
definition to declare an appropriate instances.

*)

Definition straight_line_program (type : Type)(stmt : (type -> Type) -> Type) : Program.class type
  :=  {| Program.t := fun v => list (stmt v);
         Program.monoid_instance := _
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

  Declare Instance sprogram : Program.class stype.
  Declare Instance dprogram : Program.class dtype.

  Declare Instance type_translate : Translate.class stype dtype.
  Declare Instance prog_translation {v : dtype -> Type} : Translate.class (Program.t (Translate.tr v)) (Program.t v).

End LanguageTranslate.
