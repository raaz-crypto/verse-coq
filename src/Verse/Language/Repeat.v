Require Import Verse.Monoid.

(**

Cryptographic primitives, at times need the facility of repeating a
block of unparametrized code. Providing an explicit inductive type for
this facility allows other parts of the code base, especially the
target code generation, to be cognizant of such use. This becomes
essential, for example, to keep generated code sizes in check for
elliptic curve based primitives.

 *)

Inductive repeated A : Type :=
| repeat : nat -> A -> repeated A.

Arguments repeat [A].

Polymorphic Definition Repeat A := list (repeated (list A)).

Definition unroll [A M] `{Setoid M} `{Monoid M} (f : A -> M)
  := mapMconcat (fun rla => let 'repeat n la := rla
  in ntimes n (f la)).
