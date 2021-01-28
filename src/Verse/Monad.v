(**

This is a minimal setup for monadic notations for verse. No attempt is
made to also prove the monadic laws.

*)


Class Monad (T : Type -> Type)
  := { pure : forall A, A -> T A;
       bind : forall A B, T A -> (A -> T B) -> T B
     }.


Arguments pure {T Monad A}.
Arguments bind {T Monad A B}.
Notation "x >>= y"   := (bind x y) (at level 58, right associativity).
Section Helpers.
  Context {T}`{Monad T}{A B C: Type}.

  Definition fmap (f : A -> B) (ta : T A) : T B
    := ta >>= fun a => pure (f a).

  Definition join (tta : T (T A)) : T A := tta >>= @id _.

  Definition app (tfab : T (A -> B))(ta : T A) : T B := tfab >>= fun f => fmap f ta.

  Definition inSeq (ta : T A)( tb  : T B) : T B
    := ta >>= fun _ => tb.

  Definition mcompose (fbc : B -> T C)(fab  : A -> T B) : A -> T C :=
    fun a => fab a >>= fun b => fbc b.

End Helpers.


Notation "x >> y"    := (x >>= fun _ => y)  (at level 58, right associativity).
Notation "fx >=> fy" := (mcompose fy fx) (at level 58, right associativity).
Notation "f <$>  ta"  := (fmap f ta)     (at level 56, left associativity).
Notation "tfa <*> ta" := (app tfa ta)    (at level 57, left associativity).

Notation "A ;; B" := (A >> B)
                       (at level 61, only parsing, right associativity).

Notation "'do' pat <- y ';;' z"
  := (y >>= fun (x : _) => match x with | pat => z end)
       (at level 61, pat pattern, y at next level, only parsing, right associativity).


Instance opt_monad : Monad option :=
  let bnd  := fun A B (x : option A)(f : A -> option B) =>
                match x with
                | Some a => f a
                | None => None
                end in
  {| pure := fun A (a : A) => Some a;
     bind := bnd |}.
