(** *Monoids.

An implementation of monoids.

 *)

Class Monoid t
:= { unit : t;
     oper : t -> t -> t;
     left_identity  : forall x : t, oper unit x = x;
     right_identity : forall x : t, oper x unit = x;
     associativity  : forall x y z : t, oper x (oper y z) = oper (oper x y) z
   }.


Infix "**" := oper (right associativity, at level 60).

Require List.

Instance list_is_monoid (A : Type)
  : Monoid (list A) :=
  {| unit := nil;
     oper  := List.app (A:=A);
     left_identity := List.app_nil_l (A:=A);
     right_identity := List.app_nil_r (A:=A);
     associativity := List.app_assoc (A:=A)
  |}.


(** ** State transition.

Transitions over a state space are just functions and can be given a
monoid structure. In the context of state transition it is more
natural to define the monoid multiplication in terms of the reverse
composition. We define a new notation for this and define the monoid
instance.

*)

(* begin hide *)
Require Import Basics.
(* end hide *)

Notation "f >-> g" := (compose g f) (left associativity, at level 40).


(** Now for the laws of monoid *)

Module LawsTransition.
  Definition left_identity_compose : forall A (f : A -> A),  (@id A) >-> f = f.
    trivial.
  Qed.

  Definition right_identity_compose : forall A (f : A -> A),  f >-> (@id A)  = f.
    trivial.
  Qed.

  Definition assoc_compose : forall A (f g h : A -> A), f >-> (g >-> h) = (f >-> g) >-> h.
    trivial.
  Qed.

End LawsTransition.

Import LawsTransition.


Instance transition_monoid (A : Type) : Monoid (A -> A)
  := {| unit := @id A;
        oper f g := f >-> g;
        left_identity := left_identity_compose A;
        right_identity := right_identity_compose A;
        associativity   := assoc_compose A
     |}.

(**

Monoidal version of concat. The function [mconcat] takes a list of
elements in the monoid and multiplies them to get the results

 *)


Definition mconcat {t}`{mon: Monoid t} : list t -> t
  := List.fold_right oper unit.

Definition mapMconcat {A}{t}`{mon : Monoid t} (f : A -> t) (xs : list A) : t
  := mconcat (List.map f xs).

(**  * Monoid instance A + {E}.

*)


Require Import Verse.Error.

Module ErrorMonoidLaws.

  Definition moperError {E : Prop}{A :Type}
             `{Monoid A}(ex ey : A + {E}) : A + {E}
    := match ex, ey with
       | {- x -} , {- y -} => {- x ** y -}
       | error _ , _       => ex
       | _       , error _ => ey
       end.

  Definition error_left_id {E}{A}`{Monoid A}:
    forall ex : A + {E},  moperError {-unit-} ex = ex.
    intros. destruct ex; unfold moperError;try (rewrite left_identity); trivial.
  Qed.

  Definition error_right_id {E}{A}`{Monoid A}:
    forall ex : A + {E},  moperError ex {-unit-} = ex.
    intros. destruct ex; unfold moperError;try (rewrite right_identity); trivial.
  Qed.

  Definition error_assoc {E}{A}`{Monoid A}:
    forall ex ey ez : A + {E},
      moperError ex (moperError ey ez) = moperError (moperError ex ey) ez.
    intros; destruct ex; destruct ey; destruct ez;
    unfold moperError; try (rewrite associativity); trivial.
  Qed.

End ErrorMonoidLaws.

Import ErrorMonoidLaws.

Instance error_monoid {E : Prop}{A}`{Monoid A} : Monoid (A + {E})
  := {| unit := {- unit -};
        oper := moperError;
        left_identity := error_left_id;
        right_identity := error_right_id;
        associativity := error_assoc
     |}.
