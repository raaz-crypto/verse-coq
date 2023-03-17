Require Import Verse.Monoid.
Require Import Verse.Error.
Import List.ListNotations.

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

Section Repeat.

  Context [A B : Type]
          (f : A -> B).

  Definition push (rsrc : repeated A) : repeated B
    := match rsrc with
       | repeat n s => repeat n (f s)
       end.

  Context [Err : Prop].
  Definition pullOutRep (rerr : repeated (A + {Err})) : repeated A + {Err}
    := match rerr with
       | repeat n {- x -}     => {- repeat n x -}
       | repeat _ (error err) => error err
       end.

End Repeat.

Definition once [A] : list A -> Repeat A := fun a => [ repeat 1 a ]%list.

Coercion once : list >-> Repeat.
