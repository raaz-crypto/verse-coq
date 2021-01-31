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

(** Some common helper functions. They may be given in a more general
    context, namely functors and applicatives, but for us all of these
    are only needed for Monads *)

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

(** The monadic laws.

Instances that do not satisfies the monadic laws are problematic and
can fail the intuition behind the do notation. It is therefore good to
prove the monadic laws.

*)
Section Laws.
  Context {T}(monad : Monad T).
  Definition pure_id_l : Prop := forall A B (x : A)(f : A -> T B), pure x >>= f = f x.
  Definition pure_id_r : Prop := forall A B (x : A)(f : A -> T B), pure x >>= f = f x.
  Definition bind_assoc : Prop := forall A B C (ta : T A)(f : A -> T B)(g : B -> T C),
      (ta >>= f) >>= g  = ta >>= fun x => f x >>= g.

  Definition monad_laws : Prop := pure_id_l /\ pure_id_r /\ bind_assoc.
End Laws.

Ltac crush_monad_laws :=
  unfold monad_laws;  intuition;
  unfold pure_id_l; unfold pure_id_r; unfold bind_assoc;
  intros;
  match goal with
  | [ ta : ?T _ |- _ ] => destruct ta; trivial
  | _ => trivial
  end.

(** Some common instances. *)

Instance opt_monad : Monad option :=
  let bnd  := fun A B (x : option A)(f : A -> option B) =>
                match x with
                | Some a => f a
                | None => None
                end in
  {| pure := fun A (a : A) => Some a;
     bind := bnd |}.

Lemma option_monad_laws : monad_laws opt_monad.
Proof.
  crush_monad_laws.
Qed.


(** ** Sumor type used as error. *)

Definition Error {E : Prop} : Type -> Type := fun A => A + {E}.

Instance error_monad (E : Prop) : Monad (Error) :=
  let bnd  :=
  fun A B (x : A + {E} )(f : A -> B + {E}) =>
    match x with
    | inleft a => f a
    | inright e => inright e
    end in
  {| pure := fun A =>  @inleft A E ;
     bind := bnd |}.

Lemma error_monad_laws : forall E, monad_laws (error_monad E).
  intros; crush_monad_laws.
Qed.
