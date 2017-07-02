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

(* Haskell like applicative notation for errors *)
Global Notation "F <$> A" := (ap  F A) (at level 40, left associativity).
Global Notation "F <*> A" := (apA F A) (at level 40, left associativity).
