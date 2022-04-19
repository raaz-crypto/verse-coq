(** *Monoids.

An implementation of monoids.

 *)

(* Lists in the standard library are not universe
   polymorphic. This does not work well with the
   `call` element of the Verse AST
*)
Require Import Monoid.PList.
Require Import SetoidClass.

(* TODO : Move eq_setoid and its setoids monoids to the bottom of the
          file. Will avoid errors like that happened with
          dep_point_monoid
*)

Class Monoid t `{Setoid t}
:= { ε  : t;
     oper  : t -> t -> t;
     welldef_l : forall x y z, x == y -> oper x z == oper y z;
     welldef_r : forall x y z, x == y -> oper z x == oper z y;
     left_identity  : forall x : t, (oper ε x) == x;
     right_identity : forall x : t, (oper x ε) == x;
     associativity  : forall x y z : t,
         (oper x (oper y z)) == (oper (oper x y) z)
   }.

Infix "**" := oper (right associativity, at level 60).

Definition welldef {T} `{Monoid T} w x y z
  : w == x -> y == z -> w ** y == x ** z
  := fun e f =>
       transitivity (welldef_l w x y e) (welldef_r y z x f).


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


Program Instance point_setiod A B `{Setoid B} : Setoid (A -> B) | 1 :=
  {| equiv f g := forall x, f x == g x;
     setoid_equiv := _
  |}.
Next Obligation.
  constructor.
  - unfold Reflexive; intros; setoid_reflexivity.
  - unfold Symmetric; intros; setoid_symmetry; eauto.
  - unfold Transitive; intros f g h; intros fEQg gEQh; intro x; setoid_transitivity (g x); eauto.
Qed.

Instance point_monoid A B `{Monoid B} : Monoid (A -> B) | 1.
refine {| ε      := fun _ => ε;
          oper f g  := fun x => f x ** g x;
          welldef_l := _;
          welldef_r := _;
          left_identity  := _;
          right_identity := _;
          associativity  := _;
       |}.
simpl in *.
intros.
now apply welldef_l.

simpl in *.
intros.
now apply welldef_r.

simpl.
intros.
apply left_identity.

simpl.
intros.
apply right_identity.

simpl.
intros.
apply associativity.
Defined.

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

Record isHom [t1 t2] `{Monoid t1} `{Monoid t2} (f : t1 -> t2)
  := {
       well_def  : forall {a b}, a == b -> f a == f b;
       unit_map  : f ε == ε;
       commute   : forall {a b}, f (a ** b) == (f a) ** (f b)
     }.

Arguments well_def {t1 t2 _ _ _ _ _} _ [a b].
Arguments unit_map [t1 t2] {_ _ _ _ _} _.
Arguments commute [t1 t2] {_ _ _ _ _} _.

Definition Hom t1 t2 `{Monoid t1} `{Monoid t2} := { f : t1 -> t2 & isHom f }.
Definition homFunction {t1 t2}`{Monoid t1}`{Monoid t2}(f : Hom t1 t2) : t1 -> t2 := projT1 f.

Definition Endo T `{Monoid T} := Hom T T.
Definition endoFunction {T}`{Monoid T} : Endo T -> T -> T := homFunction.
Coercion homFunction : Hom >-> Funclass.
Coercion endoFunction : Endo >-> Funclass.


Ltac hom_crush :=
  unfold compose; intros;
  repeat
    match goal with
    | [ |- isHom ?h] => exact (projT2 h)
    | [ |- ?X == ?X ] => setoid_reflexivity
    | [ |- ?h _ == ε ] => apply unit_map
    | [ _ : ?A == ?B
                   , _ : ?B == ?C
        |- ?A == ?C ] => setoid_transitivity B

    |[ |- ?h _  == ?h _ ] => apply well_def
    | H : Hom _ |- _ => destruct H
    | E : Endo _ |- _ => destruct E

                                 (*
    | [ h : Endo _  |- ?h _  == ε ]  => try (apply (unit_map (projT2 h)));
                              apply Equivalence_Symmetric;
                              rewrite <- (unit_map (projT2 h)) at 1;
                              apply (well_def (projT2 h)); apply Equivalence_Symmetric
    | [|-  ?h _  ==  ?h _ ** ?h _] => try (apply (commute (projT2 h)));
                                                 rewrite <- (commute (projT2 h))
                                *)
    | _                    => eauto
  end.


Module End.

  Lemma endo_unit_map {T}`{Monoid T}(h : Endo T)(eps : T) : (eps == ε) -> h eps == ε.
    intros;
      assert (h eps == h ε) by hom_crush;
      assert (h ε == ε) by hom_crush.
    hom_crush.
  Qed.


  Lemma endo_commute {T}`{Monoid T}(h : Endo T) : forall (a b : T),  h (a ** b) ==  h a ** h b.
    apply commute; hom_crush.
  Qed.

  Definition eq {T} `{Monoid T} (h1 h2 : Endo T)
    := (h1 : T -> T) == (h2 : T -> T).

  Definition op {T} `{Monoid T}
             (h1 h2 : Endo T) : Endo T.
    refine (existT _ (h2 >-> h1)
                  {|
                    well_def := _;
                    unit_map := _;
                    commute  := _
                  |}).
    - hom_crush.
    - unfold compose; hom_crush;
        repeat apply endo_unit_map; hom_crush.
    - intros.
      assert (h2 ( a ** b) == h2 a ** h2 b) by apply (endo_commute h2).
      assert (h1 (h2 (a ** b)) == h1 (h2 a ** h2 b)). apply well_def; hom_crush.
      assert (h1 (h2 a ** h2 b) == h1 (h2 a) ** h1 (h2 b)). apply (endo_commute h1).
      unfold compose. hom_crush.
  Defined.

  Definition id {T} `{Monoid T} : isHom id :=
    {|
      well_def := fun _ _ e => e;
      unit_map := reflexivity ε;
      commute  := fun f g => reflexivity (f ** g)
    |}.

  Instance end_setoid T `{Monoid T} : Setoid (Endo T).
  refine
  {|
    equiv := eq;
    setoid_equiv :=
      {|
        Equivalence_Reflexive := fun x : Endo T => fun _ => reflexivity _;
        Equivalence_Symmetric := fun (x y : Endo T)
                                     (H1 : eq x y) =>
                                   symmetry H1;

        Equivalence_Transitive := fun (x y z : Endo T)
                                      (H1 : eq x y)
                                      (H2 : eq y z) =>
                                    transitivity H1 H2
      |}
  |}.
  unfold Symmetric.
  intros.
  unfold eq in *.
  exact (symmetry H2).

  unfold Transitive.
  intros.
  unfold eq in *.
  exact (transitivity H3 H4).
  Defined.

  Instance end_monoid T `{Monoid T} : Monoid (Endo T).
  refine
    {| ε           := existT _ _ id;
       oper           := op;
       welldef_l      := fun x y z e => _;
       welldef_r      := fun x y z e => _;
       left_identity  := fun _ => _;
       right_identity := fun _ => _;
       associativity  := fun _ _ _ => _;
    |}.
  unfold op.
  simpl in *.
  unfold eq in *.
  simpl in *.
  destruct z.
  unfold compose.
  intro.
  apply e.

  unfold op.
  simpl in *.
  unfold eq in *.
  simpl in *.
  unfold compose.
  intro.
  trivial.

  unfold op.
  now apply (well_def (projT2 z)).

  now unfold op.

  now unfold op.

  now unfold op.
Defined.

End End.

Instance prop_monoid : Monoid Prop.
refine {| ε          := True;
          oper f g      := and f g;
          welldef_l     := _;
          welldef_r     := _;
          left_identity := _;
          right_identity := _;
          associativity := _
       |}.
all: simpl in *; intuition.
Defined.

(**

Monoidal version of concat. The function [mconcat] takes a list of
elements in the monoid and multiplies them to get the results

 *)


Definition mconcat {t}`{mon: Monoid t} : list t -> t
  := fun l => fold_left oper l ε.

Definition mapMconcat {A}{t}`{mon : Monoid t}
           (f : A -> t) (xs : list A)
  : t
  := mconcat (map f xs).

(**  * Monoid instance A + {E}.

*)


Require Import Verse.Error.

Module Sumor.

  (* Setoid *)

  Inductive eq {E A} `{Setoid A}: A + {E} -> A + {E} -> Prop :=
  | eqErr e   : eq (error e) (error e)
  | eqA a1 a2 : a1 == a2 -> eq {- a1 -} {- a2 -}
  .

  Instance eq_reflex {E : Prop} {A : Type} `{Setoid A} : Reflexive (eq (E := E))
    := fun ae => match ae with
                 | {- a -} => eqA a a (Equivalence_Reflexive a)
                 | error e => eqErr e
                 end.

  Instance eq_symm {E A} `{Setoid A} : Symmetric (eq (E := E))
    := fun ae bf r => match r in eq A B return eq B A with
                      | eqErr e => eqErr e
                      | eqA a1 a2 eqa => eqA a2 a1 (Equivalence_Symmetric a1 a2 eqa)
                      end.

  Instance eq_trans {E A} `{Setoid A} : Transitive (eq (E := E)).
  refine (fun ae bf cg r1 => match r1 with
                             | eqErr e   => id
                             | eqA _ _ _ => fun r2 => _
                             end).
  inversion r2.
  apply eqA.
  exact (Equivalence_Transitive _ _ _ e H1).
  Defined.

  (* Monoid *)

  Definition oper {A E} `{Monoid A} (ex ey : A + {E}) : A + {E}
    := match ex, ey with
       | {- x -} , {- y -} => {- x ** y -}
       | error _ , _       => ex
       | _       , error _ => ey
       end.

  Definition welldef_l {A E} `{Monoid A}
                       (ex ey ez : A + {E}) (eexy : eq ex ey)
    : eq (oper ex ez) (oper ey ez) :=
    match eexy in eq ex0 ey0 return eq (oper ex0 ez) (oper ey0 ez) with
    | eqA x y exy => match ez with
                     | {- z -} => eqA _ _ (welldef_l _ _ _ exy)
                     | error _ => eqErr _
                     end
    | eqErr e     => eqErr _
    end.

  Definition welldef_r {A E} `{Monoid A}
                       (ex ey ez : A + {E}) (eexy : eq ex ey)
    : eq (oper ez ex) (oper ez ey) :=
    match eexy in eq ex0 ey0 return eq (oper ez ex0) (oper ez ey0) with
    | eqA x y exy => match ez with
                     | {- z -} => eqA _ _ (welldef_r _ _ _ exy)
                     | error _ => eqErr _
                     end
    | eqErr e     => match ez with
                     | {- _ -} => eqErr _
                     | error _ => eqErr _
                     end
    end.

  Definition left_id {A E} `{Monoid A} :
    forall ex : A + {E},  eq (oper {-ε-} ex) ex.
    intros; destruct ex; unfold oper; constructor; try (apply left_identity).
  Qed.

  Definition right_id {A E} `{Monoid A} :
    forall ex : A + {E},  eq (oper ex {-ε-}) ex.
    intros; destruct ex; unfold oper; constructor; try (apply right_identity).
  Qed.

  Definition assoc {A E} `{Monoid A} :
    forall ex ey ez : A + {E},
      eq (oper ex (oper ey ez)) (oper (oper ex ey) ez).
    intros; destruct ex; destruct ey; destruct ez;
      unfold oper; constructor; try (apply associativity).
  Qed.

End Sumor.

Instance error_setoid {E : Prop}{A}`{Setoid A} : Setoid (A + {E}) :=
 {|
   equiv := Sumor.eq;
            setoid_equiv := {|
                             Equivalence_Reflexive := Sumor.eq_reflex (A:=A);
                             Equivalence_Symmetric := Sumor.eq_symm (A:=A);
                             Equivalence_Transitive := Sumor.eq_trans (A:=A)
                            |}
 |}.

Instance error_monoid {E : Prop}{A}`{Monoid A}
  : Monoid (A + {E}) :=
  {| ε := {- ε -};
     oper := Sumor.oper;
     welldef_l := Sumor.welldef_l;
     welldef_r := Sumor.welldef_r;
     left_identity := Sumor.left_id;
     right_identity := Sumor.right_id;
     associativity := Sumor.assoc
  |}.

Module Prod.
  Section Prod.

    Variable A B : Type.
    Variable MA  : Setoid A.
    Variable MB  : Setoid B.

    Definition eq (x y : A * B) := (fst x == fst y) /\ (snd x == snd y).

    Definition refl : Reflexive eq
      := fun x => conj (Equivalence_Reflexive (fst x)) (Equivalence_Reflexive (snd x)).

    Definition symm : Symmetric eq
      := fun x y r => let (rf, rs) := r in
                      conj (Equivalence_Symmetric _ _ rf)
                           (Equivalence_Symmetric _ _ rs).

    Definition trans : Transitive eq
      := fun x y z rxy ryz =>
               let (rxyf, rxys) := rxy in
               let (ryzf, ryzs) := ryz in
               conj (Equivalence_Transitive _ _ _ rxyf ryzf)
                    (Equivalence_Transitive _ _ _ rxys ryzs).

  End Prod.

  Arguments eq {A B MA MB}.
  Arguments refl {A B MA MB}.
  Arguments symm {A B MA MB}.
  Arguments trans {A B MA MB}.

End Prod.

Instance prod_setoid A B `{Setoid A} `{Setoid B} : Setoid (A * B)
  := {| equiv        := Prod.eq;
        setoid_equiv := {|
                         Equivalence_Reflexive := Prod.refl;
                         Equivalence_Symmetric := Prod.symm;
                         Equivalence_Transitive := Prod.trans
                        |}
     |}.

Notation action A B := (Hom A (Endo B)).

Record SemiDirectProduct = SemiDirect
Module SDP.
  Section SDP.
    Variable A B : Type.

    Definition id `{Monoid A} `{Monoid B} : A*B := (ε, ε).

    Definition oper `{Monoid A} `{Monoid B} (h : action A B)
      := fun (p q : A*B) => ((fst p) ** (fst q),
                     (snd p) ** ((h (fst p)) (snd q))).

    Definition welldefl `{Monoid A} `{Monoid B} h px py pz
      : px == py -> oper h px pz == oper h py pz.
      simpl.
      unfold Prod.eq.
      intuition.
      now apply welldef_l.

      simpl.
      unfold Prod.eq.

      intuition.

      simpl.
      apply welldef.
      trivial.

      enough (func (func h (fst px)) == func (func h (fst py))).
      trivial.

      enough (func h (fst px) == func h (fst py)).
      trivial.

      now apply (well_def (projT2 h)).
    Defined.

    Definition welldefr `{Monoid A} `{Monoid B} h px py pz
      : px == py -> oper h pz px == oper h pz py.
      simpl.
      unfold Prod.eq.
      intuition.
      now apply welldef_r.

      simpl.
      apply welldef_r.
      apply well_def.
      destruct h.
      simpl.
      destruct (x a).
      all: trivial.
    Defined.

    Definition left_identity `{Monoid A} `{Monoid B} h (x:A*B)
      : oper h id x == x.
      simpl.
      unfold Prod.eq.
      simpl.
      apply conj.
      apply left_identity.
      rewrite left_identity.
      pose (unit_map (projT2 h)).
      simpl in e.
      unfold End.eq in e.
      simpl in e.
      rewrite e.
      now unfold Datatypes.id.
    Defined.

    Definition right_identity `{Monoid A} `{Monoid B} h x
      : oper h x id == x.
      simpl.
      unfold Prod.eq.
      simpl.
      apply conj.
      apply right_identity.
      setoid_rewrite <- (right_identity (snd x)) at 2.
      apply welldef.
      reflexivity.
      apply unit_map.
      destruct h.
      simpl.
      destruct (x0 (fst x)).
      now simpl.
    Defined.

    Definition associativity `{Monoid A} `{Monoid B} h x y z
      : oper h x (oper h y z) == oper h (oper h x y) z.
      simpl.
      unfold Prod.eq.
      simpl.
      intuition.
      simpl.
      apply associativity.
      simpl.
      rewrite <- associativity.
      apply welldef_r.
      simpl End.eq.
      rewrite (commute (projT2 (func h a))).
      apply welldef_r.
      pose (commute (projT2 h) a a0).
      transitivity (func (func h a ** func h a0) b1).
      now simpl.

      enough (func h a ** func h a0 == func h (a ** a0)).
      trivial.

      now rewrite e.
    Defined.

  End SDP.
End SDP.

Instance semi_direct_prod A B `{Monoid A} `{Monoid B}
         (h : action A B)
  : Monoid (A * B)
  := {| ε := SDP.id A B;
        oper := SDP.oper _ _ h;
        welldef_l := SDP.welldefl _ _ h;
        welldef_r := SDP.welldefr _ _ h;
        left_identity := SDP.left_identity _ _ h;
        right_identity := SDP.right_identity _ _ h;
        associativity := SDP.associativity _ _ h
     |}.



Definition twist {A B} `{Monoid B} (ea : A -> A) : End (A -> B).
  refine (existT _ (fun m => ea >-> m)
                {|
                  well_def := _;
                  unit_map := _;
                  commute  := _
                |}).
  simpl in *.
  now unfold compose.
  reflexivity.
  reflexivity.
Defined.

Definition halftwist {A B} `{Monoid B} (ea : A -> A) : End (A*A -> B).
  refine (existT _ (fun m => (fun aa => (fst aa, ea (snd aa))) >->  m)
                 {|
                   well_def := _;
                   unit_map := _;
                   commute  := _
                 |}).
  simpl in *.
  now unfold compose.
  reflexivity.
  reflexivity.
Defined.

(** **

This marks the separator between definitions that should not be using
the eq_setoid and those that 'can'.

*)

Instance eq_setoid T : Setoid T | 10
  := { equiv := eq }.

Instance list_is_monoid (A : Type)
  : Monoid (list A).
refine  {| ε  := nil;
           oper  := List.app (A:=A);
           welldef_l := fun _ _ _ _ => _;
           welldef_r := fun _ _ _ _ => _;
           left_identity  := app_nil_l (A:=A);
           right_identity := app_nil_r (A:=A);
           associativity  := app_assoc (A:=A)
        |}.
all : simpl in *; rewrite e; trivial.
Defined.

Instance transition_monoid (A : Type) : Monoid (A -> A) | 0.
refine {| ε := @id A;
          oper f g := f >-> g;
          welldef_l := _ (*fun _ _ _ _ => _*);
          welldef_r := _ (*fun _ _ _ _ => _*);
          left_identity := _ (*fun _ _ => eq_refl left_identity_compose A*);
          right_identity := _ (*fun _ _ => eq_refl right_identity_compose A*);
          associativity   := _ (*assoc_compose A*)
       |}.
intros. simpl "==". unfold ">->". intro. f_equal. apply H.
intros. simpl "==". unfold ">->". intro. f_equal.
easy.
easy.
easy.

Defined.

(* The following definitions are towards giving a monoid structure for
   the Abstract Machine.

   Code there is of the type

   (state -> state) * (state * state -> Prop)

   to capture both the state transition and annotations on the state.
 *)

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
