(* An implementation of basic category theories in Coq *)

Require Import FunctionalExtensionality.
Require Import Basics.

Module Type Cat.

  (** The type of objects of the category *)
  Parameter o : Type.

  Parameter mr : o -> o -> Type.

  Parameter idM : forall {a}, mr a  a.

  Parameter composeM : forall {a b c}, (mr b c) -> (mr a b) -> (mr a c).

  Axiom identityLeft  : forall {a b}{f : mr a b}, composeM idM f =  f.

  Axiom identityRight : forall {a b}{f : mr a b},  composeM f idM =  f.

  Axiom associativity : forall {a b c d}{f : mr a b}{g : mr b c}{h : mr c d}, composeM (composeM h g) f  = composeM h (composeM g f).

End Cat.

(** The usual category of Types *)
Module TypeCat <: Cat.

  Definition o := Type.

  Definition mr := fun A B => A -> B.

  Definition idM {A}:= @id A.

  Definition composeM {A B C} := @compose A B C.

  Definition identityLeft {a b}{f : a -> b} : compose id  f = f.
  Proof.
    trivial.
  Qed.

  Definition identityRight {a b}{f : a -> b} : compose f id = f.
  Proof.
    trivial.
  Qed.

  Definition associativity {a b c d}{f : a -> b}{g : b -> c}{h : c -> d}: (compose (compose h g) f) = compose h (compose g f).
  Proof.
    trivial.
  Qed.

End TypeCat.

Module Type Functor (C : Cat) (D : Cat).

  Parameter omap : C.o -> D.o.

  Parameter mmap : forall {a b : C.o}, (C.mr a b) -> (D.mr (omap a) (omap b)).

  Axiom idF : forall (a : C.o), mmap (@C.idM a) = @D.idM _.

  Axiom functorial : forall {a b c : C.o} (g : C.mr b c) (f : C.mr a b),
      mmap (C.composeM g f) = D.composeM (mmap g) (mmap f).
  
End Functor.



  

