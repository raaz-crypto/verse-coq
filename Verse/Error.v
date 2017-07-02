
Definition ap {A B : Type}{Err : Prop}(f : A -> B) (y : A + {Err}) :=
  match y with
  | inleft  a    => inleft (f a)
  | inright err  => inright err
  end.



Definition recover {A : Type}{Err : Prop}(x : A + {Err}) : if x then A else Err
  := match x with
     | inleft a => a
     | inright b => b
     end.
