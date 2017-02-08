Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import FunctionalExtensionality.
Require Import Basics.

(** * Syntactic types.

In this module, we define coq types that captures various syntactic
objects in verse namely variables, languages, substitutions etc.


*)

(** ** Variable type.


Programs use variables.  The type [varT : Type] captures coq types
that can potentially be variables in programs.  A user first defines
an inductive type whose constructors are the variable she intends to
use in the program. For example, suppose she wishes to write a program
which use two variables A and B of types [Word32] and [Word64]
respectively, she would begin with a definition of the following
nature:


<<

Inductive Var : varT :=
| A : Var Word32
| B : Var Word64
.

>>


Defining variables as above helps the user avoid problems like name
clashing (guranteed by each constructor being a name).

*)

Definition varT := type -> Type.

(** ** Substitution type.

The type [subT u v] is the coq type that captures substitutions from
variables of type [u] to variables of type [v]

*)

Definition subT (u v : varT) := forall t, u t -> v t.


(** For any variable type [u : varT] there is always a identity substitution *)

Definition idSubst (u : varT) : subT u u := fun _ x => x.

(** Substitutions can be composed *)
Definition composeSubT {u v w} (g : subT v w)(f : subT u v) : subT u w :=
  fun t ut => g t (f t ut).

Arguments composeSubT [u v w].

Notation "f >> g" := (composeSubT g f) (at level 40, left associativity).
Notation "f << g" := (composeSubT f g) (at level 40, left associativity).



(** ** Syntactic types.

The type [synT : Type] captures the coq type of syntax trees. If
[progLang : synT], a syntactic type then [prog : progLang] can be seen
as a particular program parameteried by variables, i.e. if in addition
[u : varT], then [prog u] is a fragment that uses the variable type
[u].

*)

Definition synT := varT -> Type.

(** *** The class of abstract syntax trees.

Not all elements of [synT] are valid syntax trees. The class [AST]
captures those syntactic objects that are abstract syntax trees. There
are types that allow mapping over its variables using a substitution.

*)

Class AST (syn : synT) :=
  {
    (** Change variables according to substitution **)
    map         {u v}                               : subT u v -> syn u -> syn v;

    (** The identity law of map *)
    identity    {u}                                 : map (idSubst u) = id;

    (** The law of composition *)
    composition {u v w}{g : subT v w}{f : subT u v} : compose (map g) (map f) = map (g << f)
  }.
