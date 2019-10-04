
(** * Representing Erros.

    We use the sumor type to represent constructs in the verse
language that might be erroneous. This module developes the monadic
notation for it for ease of use in the rest of the program.

*)


Global Notation "{- A -}" := (inleft A).
Global Notation "'error' A" := (inright A) (at level 40).

Section Error.
  Variable A   : Type.
  Variable Err : Prop.

  Section Apply.
    Variable B   :  Type.
    Definition ap (f : A -> B) (y : A + {Err}) :=
      match y with
      | {- a -}    => {- f a -}
      | inright err  => inright err
      end.

    Definition apA (f : (A -> B) + {Err})(x : A + {Err}) :  B + {Err} :=
      match f, x with
      | {- f -} , {- x -}  => {- f x -}
      | inright e, _         => inright e
      | _        , inright e => inright e
      end.

    Definition bind (x : A + {Err})(f : A -> B + {Err}) : B + {Err} :=
      match x with
      | {- a -} => f a
      | inright e => inright e
      end.

  End Apply.

  Definition TypeE := Type + {Err}.

  Definition inject (A : TypeE) : Type :=
    match A with
    | {- T -} => T
    | _       => Empty_set + {Err}
    end.

  Definition lift (fam : A -> Type) : A + {Err} -> Type
    := fun ae => inject (ap Type fam ae).

  Section DependentApply.

    Variable fam : A -> Type.

    Definition apD (f : forall a, fam a) : forall y, lift fam y
      := fun y =>
           match y as y0 return lift fam y0 with
           | {- a -} => f a
           |  error e => error e
           end.


  End DependentApply.

  Definition recover (x : A + {Err}) : if x then A else Err
    := match x with
       | {- a -} => a
       | inright b => b
       end.

  Definition noErrorIsNotError {e : Err} {a : A}  : error e <> inleft a.
    intro pf.
    refine (match pf with
            |eq_refl => _
            end); exact idProp.
  Defined.

  Definition recover' (ae : A + {Err}) : (exists a, ae = inleft a) -> { a : A | ae = inleft a}
    := match ae as ae0 return (exists a, ae0 = {- a -}) -> {a | ae0 = {- a -} } with
       | inleft a  => fun _  => exist _ a eq_refl
       | inright _ =>
         let absurdity pf :=  match pf with
                              | ex_intro _ _ pf0 => noErrorIsNotError pf0
                              end in
         fun pf => False_rect _ (absurdity pf)
       end.


End Error.
Arguments recover' [A Err].

(* Type to capture translation error *)
Inductive TranslationError : Prop :=
| CouldNotTranslate : forall A : Type, A -> TranslationError
| CouldNotTranslateBecause : forall A : Type, A -> TranslationError -> TranslationError.

Arguments  CouldNotTranslate [A].
Arguments  CouldNotTranslateBecause [A].


Notation "'could' 'not' 'translate' X" := (CouldNotTranslate  X) (at level 100, only printing).
Notation "'unable' 'to' 'translate' X 'because,' E"
  := (CouldNotTranslateBecause X E)
       ( at level 101, right associativity, only printing,
         format "'[v   ' 'unable'  'to'  'translate'  X  'because,' '/' E ']'"
       ).

(*
Section Extract.

  Variable T : Type.
  Variable E : Prop.

  Definition noErr (x : T + {E}) : Prop := exists t : T, x = inleft t.

  Definition isErr (x : T + {E}) : { noErr x } + { ~ noErr x }.
    refine (match x as y return x = y -> {noErr x} + {~ noErr x} with
            | {- t -} => fun p => left (ex_intro _ t p)
            | error e => fun p => right _
            end eq_refl).
    destruct 1 as [y H]. rewrite p in H. discriminate H.
  Defined.

  Definition getT (x : T + {E}) (p : noErr x) : T.
    refine (match x as y return noErr y -> T with
            | {- t -} => fun _ => t
            | error e => _
            end p).
    unfold noErr.
    intro H; contradict H;
      destruct 1; discriminate.
  Defined.

  Lemma getTgetsT (x : T + {E}) (p : noErr x) : x = {- getT x p -}.
    destruct p.
    rewrite e.
    trivial.
  Defined.

  Lemma getTunique (x : T + {E}) (p1 p2 : noErr x) : getT x p1 = getT x p2.
    destruct (x).
    simpl; trivial.
    contradict p1; destruct 1; discriminate.
  Defined.

End Extract.
*)

Class Castable (E1 E2 : Prop) := { cast : E1 -> E2 }.

Instance idCast E : Castable E E := { cast := @id _ }.

Section Lifts.

  Variable T    : Type.
  Variable E E1 E2 : Prop.

  Variable E1toE : Castable E1 E.
  Variable E2toE : Castable E2 E.

  Definition liftErr (t : T + {E1}) : T + {E} :=
    match t with
    | {- t' -} => {- t' -}
    | error e  => error (cast e)
    end.

  Definition collectErr (t : T + {E1} + {E2}) : T + {E} :=
    match t with
    | error e2       => error (cast e2)
    | {- error e1 -} => error (cast e1)
    | {- {- t' -} -} => {- t' -}
    end.

End Lifts.

Arguments liftErr [T E E1 _] _.
Arguments collectErr [T E E1 E2 _ _] _.

Section Conditionals.

  (** Some type *)
  Variable A : Type.

  (** A decidable predicate on A *)
  Variable P : A -> Prop.

  (** The decision procedure for P *)
  Variable decP : forall a : A, {P a} + {~ P a}.

  (** Emit the value only whe the predicate is satisfied
   *)
  Definition when (a : A) : A + {~ P a} :=
    match decP a with
    | left _  => {- a -}
    | right err => error err
    end.

  (** Emit the value unless the predicate is true. *)
  Definition unless (a : A ) : A + {P a} :=
    match decP a with
    | left err => error err
    | right _ => {- a -}
    end.

End Conditionals.

Arguments when [A P] _ _.
Arguments unless [A P] _ _.
Arguments ap [A Err B] _ _.
Arguments apD [A Err fam].
Arguments apA [A Err B] _ _.
Arguments recover [A Err] _.
Arguments bind [A Err B] _ _.
(* Haskell like applicative notation for errors *)
Global Notation "F <$> A" := (ap  F A) (at level 40, left associativity).
Global Notation "F <*> A" := (apA F A) (at level 40, left associativity).
Global Notation "X <- A ; B" := (bind A (fun X => B))(at level 81, right associativity, only parsing).
Global Notation "X *<- A ; B" := (bind (liftErr A) (fun X => B))(at level 81, right associativity, only parsing).

Section Merge.
  Require Import Vector.
  Import VectorNotations.

  Variable A : Type.
  Variable Err : Prop.

  Fixpoint mergeVector {n} (verr : Vector.t (A + {Err}) n) : Vector.t A n + {Err} :=
  match verr with
  | []                            => {- [] -}
  | inright err :: _              => inright err
  | Vector.cons _ {- x -} m xs => Vector.cons _ x m  <$> (@mergeVector m xs)
  end.

  Require Import List.
  Import ListNotations.
  Fixpoint merge (actions : list (A + {Err})) : list A + {Err} :=
    match actions with
    | nil => {- nil -}
    | error err :: _ => inright err
    | cons {- x -} xs  => cons x <$> merge xs
    end.
End Merge.

Section PartialFunctions.
  Variable A B : Type.
  Variable E   : Prop.
  Variable partial : A -> B + {E}.


  Definition InDomain a := exists b, partial a = inleft b.
  Definition InRange  b := exists a, partial a = inleft b.

  Definition domain := {a | InDomain a}.
  Definition range  := {b | InRange b}.

  Definition totalise (aD : domain) : B :=
    match aD with
    | exist _ a pf
      => match recover' (partial a) pf with
         | exist _ b _ => b
         end
    end.

  (* Get the total core of the partial function *)
  Definition totalCore (aD : domain) : range :=
    match aD with
    | exist _ a pf =>
      match recover' (partial a) pf with
      | exist _ b pf0 => exist _ b (ex_intro _ a pf0)
      end
    end.


End PartialFunctions.
Arguments InDomain [A B E].
Arguments InRange  [A B E].
Arguments totalCore [A B E].
