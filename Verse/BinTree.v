(** * Complete binary tree *)
Require List.
Require Import Verse.Error.
Import List.ListNotations.

Section Def.
  Variable A    : Type.
  Inductive Bin : nat -> Type :=
  | leaf             : A -> Bin 0
  | node { n : nat } : Bin n -> Bin n -> Bin (S n)
  .

  Fixpoint mergeP (n : nat)(ls : list A) : option (Bin n * list A) :=
    match n, ls with
      | _ , nil        => None
      | 0 , cons x ls  => Some (leaf x, ls)
      | (S n), _
        => match mergeP n ls with
             | None           => None
             | Some (t1, ls1)
               => match mergeP n ls1 with
                    | None            => None
                    | Some (t2, ls2)  => Some (node t1 t2, ls2)
                  end
           end
    end.


  Definition merge {n : nat}(ls : list A) : option (Bin n) :=
    match mergeP n ls with
      | Some (x, nil) => Some x
      | Some (x, _ )  => None
      | None          => None
    end.

  Inductive MergeError := ErrorOnMerge.
  Definition mergeE {n : nat}(ls : list A)
    := optionToError ErrorOnMerge (@merge n ls).
End Def.

Arguments merge  [A] [n] ls.
Arguments mergeE [A] [n] ls.
