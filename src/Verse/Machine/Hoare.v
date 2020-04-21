
(** * Assertions and Hoare Logic.

An assertion at any given point in the program is just a Prop valued
function on the state.

*)

Require Import Verse.Monoid.
Require Import Verse.Machine.
Section Hoare.
  Variable cxt : context.

  Definition assertion := state cxt -> Prop.

  (** The Hoare triple *)
  Definition triple
             (P    : assertion)
             (prog : program cxt)
             (Q    : assertion) :=
    forall st : state cxt, P st -> Q (prog st).

  Notation "{{ P }} prog {{ Q }}" := (triple P prog Q) (at level 90).
  Notation "⦃ P ⦄ prog ⦃ Q ⦄" := (triple P prog Q) (only printing, at level 90).

End Hoare.
Arguments triple [cxt].
