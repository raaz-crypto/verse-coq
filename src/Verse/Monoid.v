(** *Monoids.

An implementation of monoids.

 *)

(* Lists in the standard library are not universe
   polymorphic. This does not work well with the
   `call` element of the Verse AST
*)
Require Import Monoid.PList.
Require Import SetoidClass.
Require Export Setoid.
Require Import RelationClasses.
Require Export Relation_Definitions.


(* TODO : Move eq_setoid and its setoids monoids to the bottom of the
          file. Will avoid errors like that happened with
          dep_point_monoid
*)

Class BinOp (t : Type) := binop : t -> t -> t.
Infix "**" := binop (right associativity, at level 60).



Class Monoid t `{Setoid t} `{BinOp t}
  := { ε  : t;
       proper_oper    : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) binop;
       left_identity  : forall x : t, (ε ** x) == x;
       right_identity : forall x : t, (x ** ε) == x;
       associativity  : forall x y z : t,
           (x ** (y ** z)) == ((x ** y) ** z)
     }.

Ltac intro_destruct := let x := fresh "x" in (intro x; destruct x; simpl).

Ltac crush_monoid :=
  repeat match goal with
         | [ H1 : False |- _ ] => intuition
         | [ _ :  _ = ?X,  _ : ?X = _ |- _ = _ ] => intros; transitivity X; eauto
         | [ _ :  _ == ?X,  _ : ?X == _ |- _ == _ ] => intros; transitivity X; eauto
         | [ H : ?X == _ |- context[?X] ] => rewrite H
         | [ |- context[ε] ] => try (rewrite left_identity); try (rewrite right_identity)
         | _ => intuition; try (apply associativity)
         end.

Ltac crush_morph_tac n :=
  do n (do 2 intro_destruct; let hyp := fresh "eqhyp" in intro hyp); crush_monoid.

Tactic Notation "crush_morph" integer(n) := (crush_morph_tac n).

(** It should be possible to rewrite with monoid equivalence and
    operation. For this we register the underlying setoid equivalence
    and declare the monoid operation as a morphism *)

Add Parametric Relation T  (tsetoid : Setoid T)(bop : BinOp T)`{ _ : @Monoid T tsetoid bop} : T  (SetoidClass.equiv)
    reflexivity proved by (setoid_refl tsetoid)
    symmetry proved by (setoid_sym (sa:=tsetoid) )
    transitivity proved by (setoid_trans (sa:=tsetoid) ) as monoid_equivalence.

Add Parametric Morphism T `{Monoid T} : binop with signature
    (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) as binop_mor.
Proof.
  exact proper_oper.
Qed.
(*Instance oper_proper T `{Monoid T}
  : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) binop
  := proper_oper.
*)


Definition mconcat {t}`{mon: Monoid t} : list t -> t
  := fun l => fold_left binop l ε.

Definition mapMconcat {A}{t}`{mon : Monoid t}
           (f : A -> t) (xs : list A)
  : t
  := mconcat (map f xs).

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

  Definition assoc_compose' : forall A (f g h : A -> A), (h >-> g) >-> f = h >-> (g >-> f).
    trivial.
  Qed.


End LawsTransition.

Import LawsTransition.



Section FunctionEquivalence.
  Context {B : Type}`{Setoid B}{A : Type}.
  Definition equiv_function : relation (A -> B) := fun (f g : A -> B) => forall x, f x == g x.
  Lemma equiv_function_refl : reflexive _ equiv_function.
    intros f x. reflexivity.
  Qed.

  Lemma equiv_function_symm : symmetric _ equiv_function.
    intros f g fEg x.
    symmetry; eauto.
  Qed.

  Lemma equiv_function_transitive : transitive _ equiv_function.
    intros f g h fEg gEh x; transitivity (g x); eauto.
  Qed.

  Add Parametric Relation : (A -> B) equiv_function
    reflexivity proved by equiv_function_refl
    symmetry proved by equiv_function_symm
    transitivity proved by equiv_function_transitive
  as function_equivalence.

End FunctionEquivalence.


Instance function_setoid B `{Setoid B} A : Setoid (A -> B) | 1 :=
  {| SetoidClass.equiv := equiv_function;
     setoid_equiv := function_equivalence
  |}.

Section FunctionEquivalence.
  Context {B : Type}`{Monoid B}{A : Type}.
  Definition function_product (f g : A -> B) : A -> B := fun x => f x ** g x.

  Add Parametric Morphism : function_product with signature
      (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) as function_product_mor.
  Proof.
    intros f g fEQg fp gp fEQgP; intro.
    unfold function_product. rewrite (fEQg x). rewrite (fEQgP x); reflexivity.
  Qed.

End FunctionEquivalence.

Instance function_binop A B `{Monoid B} : BinOp (A -> B) :=
  fun f g x => f x ** g x.

Program Instance function_monoid A B `{Monoid B} : Monoid (A -> B) | 1 :=
  {| ε              := fun _ => ε;
     proper_oper    := function_product_mor_Proper;
     left_identity  := _;
     right_identity := _;
     associativity  := _;
  |}.

Next Obligation.
  unfold equiv_function; intros;apply left_identity.
Qed.

Next Obligation.
  unfold equiv_function; intros; apply right_identity.
Qed.

Next Obligation.
  unfold equiv_function.
  intros. apply associativity.
Qed.

(* TODO
Instance dep_point_setoid A (F : A -> Type)
         `{forall a, Setoid (F a)}
  : Setoid (forall a, F a) | 2 :=
  {| equiv f g := forall x, f x == g x;
     setoid_equiv := {|
                      Equivalence_Reflexive := fun f a =>
                                                 reflexivity (f a);
                      Equivalence_Symmetric := fun (f g : forall a, F a)
                                                   (H :
                                                      forall a : A,
                                                        f a == g a)
                                                   (a : A) =>
                                                 symmetry (H a);
                      Equivalence_Transitive := fun (f g h : forall a, F a)
                                                    (Hfg :
                                                       forall a : A,
                                                         (f a == g a))
                                                    (Hgh :
                                                       forall a : A,
                                                         (g a == h a))
                                                    (a : A) =>
                                                  transitivity (Hfg a) (Hgh a)
                    |}
  |}.

Instance dep_point_monoid A (F : A -> Type)
         `{forall a, Setoid (F a)}
         `{forall a, Monoid (F a)}
  : Monoid (forall a, F a) | 2.
refine {| ε := fun _ => ε;
          oper f g  := fun x => f x ** g x;
          welldef_l := _;
          welldef_r := _;
          left_identity  := _;
          right_identity := _;
          associativity  := _;
       |}.

simpl in *.
intros.
apply (welldef_l (Monoid := H0 x0)).
apply H1.

simpl in *.
intros.
apply (welldef_r (Monoid := H0 x0)).
apply H1.

simpl.
intros.
apply (left_identity (Monoid := H0 x0)).

simpl.
intros.
apply (right_identity (Monoid := H0 x0)).

simpl.
intros.
apply (associativity (Monoid := H0 x0)).

Defined.
 *)


Class Hom [t1 t2]`{Monoid t1} `{Monoid t2} (f : t1 -> t2) : Prop
  := { proper_morphism  : Proper (SetoidClass.equiv ==> SetoidClass.equiv) f;
       preserves_unit      : f ε == ε;
       preserves_product   : forall {a b}, f (a ** b) == f a ** f b
     }.

Instance monoid_homomorphism_Proper t1 t2 (f : t1 -> t2) `{Hom t1 t2 f} : Proper (SetoidClass.equiv ==> SetoidClass.equiv) f
  := proper_morphism.

Arguments preserves_unit [t1 t2] {_ _ _ _ _} _.
Arguments preserves_product [t1 t2] {_ _ _ _ _} _.

(**

Monoidal version of concat. The function [mconcat] takes a list of
elements in the monoid and multiplies them to get the results

 *)


(**  * Monoid instance A + {E}.

*)


Require Import Verse.Error.

Section Error.
  Context {E : Prop}{A : Type}`{Monoid A}.

  Definition eq_error (x y : A + {E}) : Prop :=
    match x , y with
    | error xe, error ye => xe = ye
    | {- xa -}, {- ya -} => xa == ya
    | _, _               => False
    end.

  Lemma eq_error_refl : Reflexive eq_error.
  Proof.
    intro; destruct x; simpl; reflexivity.
  Qed.

  Lemma eq_error_sym : Symmetric  eq_error.
  Proof.
    intros x y; destruct x; destruct y; simpl;
      repeat intuition.
  Qed.

  Lemma eq_error_trans : Transitive eq_error.
  Proof.
    do 3 intro_destruct; crush_monoid.
  Qed.

  Add Parametric Relation : (A + {E}) eq_error
      reflexivity proved by eq_error_refl
      symmetry proved by eq_error_sym
      transitivity proved by eq_error_trans as error_equivalence.

  Instance error_setoid : Setoid (A + {E}) :=
    {| SetoidClass.equiv :=  eq_error;
       SetoidClass.setoid_equiv := error_equivalence
    |}.

  Definition error_prod (x y : A + {E}) : A + {E} :=
    match x, y with
    | {- a -}, {- b -}  => {- a ** b -}
    | error e, _       => error e
    | _      , error e => error e
    end.


  Add Parametric Morphism : error_prod with signature
      (eq_error ==> eq_error ==> eq_error) as error_prod_mor.
  Proof.
    crush_morph 2.
  Qed.

  Instance binop_error : BinOp (A + {E}) := error_prod.

  Program Instance error_monoid
  : Monoid (A + {E}) :=
  {| ε := {- ε -};
     left_identity := _;
     right_identity := _;
     associativity := _;
  |}.



  Next Obligation.
    destruct x; simpl; trivial; apply left_identity.
  Qed.
  Next Obligation.
    destruct x; simpl; trivial; apply right_identity.
  Qed.

  Next Obligation.
    destruct x; destruct y; destruct z; simpl; trivial;apply associativity.
  Qed.

End Error.

Section Prod.

  Context (A B : Type)`{Monoid A} `{Monoid B}.
  Definition eq_prod (x y : A * B) := (fst x == fst y) /\ (snd x == snd y).

  Definition eq_prod_refl : Reflexive eq_prod
      := fun x => conj (Equivalence_Reflexive (fst x)) (Equivalence_Reflexive (snd x)).

  Definition eq_prod_symm : Symmetric eq_prod
      := fun x y r => let (rf, rs) := r in
                      conj (Equivalence_Symmetric _ _ rf)
                           (Equivalence_Symmetric _ _ rs).

  Definition eq_prod_trans : Transitive eq_prod
      := fun x y z rxy ryz =>
               let (rxyf, rxys) := rxy in
               let (ryzf, ryzs) := ryz in
               conj (Equivalence_Transitive _ _ _ rxyf ryzf)
                    (Equivalence_Transitive _ _ _ rxys ryzs).

  Add Parametric Relation : (A * B)%type  eq_prod
      reflexivity proved by eq_prod_refl
      symmetry proved by eq_prod_symm
      transitivity proved by eq_prod_trans as prod_equivalence.

  Instance prod_setoid  : Setoid (A * B)
    := {| SetoidClass.equiv        := eq_prod; |}.



  Instance prod_binop : BinOp (A * B) := fun x y => (fst x ** fst y, snd x ** snd y).

  Add Parametric Morphism : binop with signature
      eq_prod ==> eq_prod ==> eq_prod
        as product_binop_mor.
    unfold eq_prod.
    crush_morph 2.
  Qed.

  Program Instance prod_monoid : Monoid (A * B) :=
    {| ε := (ε, ε);
       left_identity := _;
       right_identity := _;
       associativity := _
    |}.
  Next Obligation.
    unfold eq_prod; simpl; crush_monoid.
  Qed.

  Next Obligation.
    unfold eq_prod; simpl; crush_monoid.
  Qed.

  Next Obligation.
    unfold eq_prod; simpl; crush_monoid.
  Qed.


End Prod.
Class RActionOp A G := ract : A -> G -> A.
Infix "↑" := (ract) (left associativity, at level 59).
(* For Right action the exponential notation is natural
and hence we use the up arrow as the assoiciated infix operator *)

(* TODO MAYBE:

One can also capture left action but since our application is for
transforms acting on state predicates, we only capture right actions
as of now

<<

Class LActionOp A B := lact : A -> B -> B.
Infix "•" := (lact) (right associativity, at level 59).

>>

 *)


Class RAction A G `{Monoid A}`{Monoid G}`{RActionOp A G} :=
  { proper_raction
    : Proper (SetoidClass.equiv (A:=A) ==> SetoidClass.equiv (A:=G) ==> SetoidClass.equiv (A:=A)) ract;
    ract_unit                : forall g, ε ↑ g == ε;
    ract_preserve_product  : forall a1 a2 g, (a1 ** a2) ↑ g == a1 ↑ g ** a2 ↑ g;
    ract_trivial           : forall a, a ↑ ε == a;
    ract_compose           : forall a g1 g2, a ↑ (g1 ** g2) == a ↑ g1 ↑ g2
  }.

Instance monoid_action_Proper A G `{RAction A G}
  : Proper (SetoidClass.equiv (A:=A) ==> SetoidClass.equiv (A:=G) ==> SetoidClass.equiv(A:=A)) ract
  := proper_raction.


Inductive SemiR G A := semiR : G -> A -> SemiR G A.
Infix "⋉" := SemiR (left associativity, at level 59).

Arguments semiR {G A}.

Section SemiDirectProduct.

  Context {G A : Type}
          `{RAction A G}.

  Definition eqSemiR (s1 s2 : G ⋉ A) :=
    match s1, s2 with
    | semiR g1 a1, semiR g2 a2 =>
      g1 == g2 /\ a1 == a2
    end.

  Definition eqsemi_refl : Reflexive eqSemiR.
    unfold Reflexive.
    intro_destruct. crush_monoid.
  Qed.

  Definition eqsemi_sym : Symmetric eqSemiR.
    unfold Symmetric.
    do 2 intro_destruct; crush_monoid.
  Qed.

  Definition eqsemi_trans : Transitive eqSemiR.
    unfold Transitive.
    do 3 intro_destruct; crush_monoid.
  Qed.

  Add Parametric Relation : (G ⋉ A) eqSemiR
      reflexivity proved by eqsemi_refl
      symmetry proved by eqsemi_sym
      transitivity proved by eqsemi_trans as semiR_equiv.

  Instance rsemi_direct_product : BinOp (G ⋉ A) :=
    fun s1 s2 => match s1, s2 with
              | semiR g1 a1, semiR g2 a2 => semiR (g1 ** g2) (a1 ↑ g2 ** a2)
              end.


  Instance semiRSetoid : Setoid (G ⋉ A) :=
    {| SetoidClass.equiv := eqSemiR |}.

  Add Parametric Morphism : binop with signature
      SetoidClass.equiv ==>
                        SetoidClass.equiv  ==> SetoidClass.equiv
        as rsemi_direct_product_mor.
    crush_morph 2.
  Qed.

  Program Instance semiR_monoid : Monoid (G ⋉ A) :=
    {| ε := semiR ε ε;
       left_identity := _;
       right_identity := _;
       associativity := _;
    |}.

  Next Obligation.
    destruct x as [g a];
      simpl; crush_monoid;
    rewrite (ract_unit g); crush_monoid.
  Qed.

  Next Obligation.
    destruct x as [g a]; simpl;
      crush_monoid;
      rewrite (ract_trivial a); crush_monoid.
  Qed.

  Next Obligation.
    destruct x as [g a];
      destruct y as [h b];
      destruct z as [k c]; simpl.
    crush_monoid.
    rewrite (ract_compose a h k).
    rewrite (ract_preserve_product (a ↑ h) b k).
    crush_monoid.
  Qed.

End SemiDirectProduct.

(** **

This marks the separator between definitions that should not be using
the eq_setoid and those that 'can'.

*)

Instance eq_setoid T : Setoid T | 10
  := { equiv := eq }.

Instance list_append_binop (A : Type) : BinOp (list A) := List.app (A :=A).

Instance list_is_monoid (A : Type)
  : Monoid (list A) := {| ε  := nil;
                          left_identity  := app_nil_l (A:=A);
                          right_identity := app_nil_r (A:=A);
                          associativity  := app_assoc (A:=A)
                       |}.


Instance transition_binop (A : Type) : BinOp (A -> A) :=  fun (f g : A -> A) => compose g f.
Instance transition_setoid (A : Type) : Setoid (A -> A) :=
  {| SetoidClass.equiv := eq |}.
Add Parametric Morphism A : binop with signature
    SetoidClass.equiv (A:= A -> A)==> SetoidClass.equiv  ==> SetoidClass.equiv
      as transition_mor.
  crush_monoid.
Qed.

Program Instance transition_monoid (A : Type) : Monoid (A -> A) :=
  {| ε := @id A |}.

(* The following definitions are towards giving a monoid structure for
   the Abstract Machine.

   Code there is of the type

   (state -> state) * (state * state -> Prop)

   to capture both the state transition and annotations on the state.
 *)

(*
Definition comp A B `{Monoid B} : action (A -> A) (A -> B).
  refine (existT _ twist
                 {|
                   well_def := _;
                   unit_map := _;
                   commute  := _
                 |}).
unfold twist.
simpl.
unfold End.eq.
simpl.
intros.
unfold ">->".
now rewrite H1.

easy.
easy.
Defined.

Definition halfcomp A B `{Monoid B} : action (A -> A) (A*A -> B).

  refine (existT _ halftwist
                 {|
                   well_def := _;
                   unit_map := _;
                   commute  := _
                 |}).

simpl.
unfold halftwist.
unfold End.eq.
simpl.
unfold ">->".
intros.
now rewrite H1.

simpl.
unfold End.eq.
unfold halftwist.
simpl.
unfold id.
unfold compose.
intros.
now rewrite <- (surjective_pairing).

now unfold halftwist.

Defined.

Instance sdp_halfcomp A B `{Monoid B} : Monoid ((A -> A)*(A*A -> B))
  := semi_direct_prod _ _ (halfcomp A B).
*)

Require List.
Import List.ListNotations.

Goal [1 ; 2] ** [2 ; 3] = [1 ; 2 ; 2 ; 3].  (* This computes *)
  trivial.
Qed.


Compute ([1] , [1]) ** ([2] , [2]).
Compute  {- [1] -} ** error I.

(*

Goal ([1] , [1]) ** ([2] , [2]) = ([1 ; 2] , [1; 2]).
Goal {- [1] -} ** error I = error I. (* this leads to unresloved BinOp *)

*)
