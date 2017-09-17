(** * Representing Erros.

    We use the sumor type to represent constructs in the verse
language that might be erroneous. This module developes the monadic
notation for it for ease of use in the rest of the program.

*)

Require Import Vector.
Import VectorNotations.
Section Error.
  Variable A   : Type.
  Variable Err : Prop.


  Section Apply.
    Variable B   : Type.
    Definition ap (f : A -> B) (y : A + {Err}) :=
      match y with
      | inleft  a    => inleft (f a)
      | inright err  => inright err
      end.

    Definition apA (f : (A -> B) + {Err})(x : A + {Err}) :  B + {Err} :=
      match f, x with
      | inleft f , inleft x  => inleft (f x)
      | inright e, _         => inright e
      | _        , inright e => inright e
      end.

    Definition bind (x : A + {Err})(f : A -> B + {Err}) : B + {Err} :=
      match x with
      | inleft a => f a
      | inright e => inright e
      end.

  End Apply.
  Definition recover (x : A + {Err}) : if x then A else Err
    := match x with
       | inleft a => a
       | inright b => b
       end.

End Error.


Arguments ap [A Err B] _ _.
Arguments apA [A Err B] _ _.
Arguments recover [A Err] _.
Arguments bind [A Err B] _ _.
(* Haskell like applicative notation for errors *)
Global Notation "F <$> A" := (ap  F A) (at level 40, left associativity).
Global Notation "F <*> A" := (apA F A) (at level 40, left associativity).
Global Notation "X <- A ; B" := (bind A (fun X => B))(at level 81, right associativity, only parsing).

Section Combine.
  Variable A : Type.
  Variable Err : Prop.

  Fixpoint combine  {n} (verr : Vector.t (A + {Err}) n) : Vector.t A n + {Err} :=
  match verr with
  | []                            => inleft []
  | inright err :: _              => inright err
  | Vector.cons _ (inleft x) m xs => Vector.cons _ x m  <$> (@combine m xs)
  end.

End Combine.

Arguments combine [A Err n] _.
