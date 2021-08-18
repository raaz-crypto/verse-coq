Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Ast.
Require Import Verse.Language.Pretty.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.PList.

Import ListNotations.

Require Import EqdepFacts.
Import EqNotations.

Declare Scope annotation_scope.
Delimit Scope annotation_scope with annot.

Section Annotated.

  Variable tyD : typeDenote verse_type_system.

  Definition Rel (ty : typeOf verse_type_system direct)
    := typeTrans tyD ty -> typeTrans tyD ty -> Prop.

  Variable Rels : forall (ty : typeOf verse_type_system direct),
      Rel ty -> Prop
  .

  Inductive noRels : forall (ty : typeOf verse_type_system direct),
      Rel ty -> Type :=
  .

  Section ParamV.

    Variable v : Variables.U verse_type_system.
    Arguments v [k].

    Inductive doubled : Variables.U verse_type_system :=
    | CUR k ty :> v ty -> doubled k ty
    | OLD k ty : v ty -> doubled k ty
    .

    Arguments CUR [k ty].
    Arguments OLD [k ty].

    Global Instance v_to_expdv ty : EXPR doubled ty (v ty)
      := fun t => valueOf (var (CUR t)).

    Definition expr  T := Ast.expr  doubled T.
    Definition lexpr T := Ast.lexpr doubled T.

    Definition leval {T} (l : lexpr T) `{State _ v tyD} {st : StoreP str}
      : typeTrans tyD T
      := let val2 {k} {ty} (x : doubled k ty) := match x with
                                            | CUR x => VAL x
                                            | OLD x => OLDVAL x
                                            end
         in
         match l with
         | Ast.var reg     => val2 reg
         | Ast.deref v idx => Vector.nth_order
                                (rew [id] arrayCompatibility tyD _ _ _
                                  in
                                    val2 v)
                                (proj2_sig idx)
         end.

    Fixpoint evalE {T} `{State _ v tyD} {st : StoreP str} (e : expr T)
      :  typeTrans tyD T
      := match e with
         | Ast.cval c => constTrans tyD c
         | Ast.valueOf lv => leval lv
         | Ast.binOp o e0 e1 => (opTrans tyD o) (evalE e0) (evalE e1)
         | Ast.uniOp o e0    => (opTrans tyD o) (evalE e0)
         end.


    Inductive VProp : Type :=
    | eq  : forall ty, expr ty -> expr ty -> VProp
    | rel : forall ty rel, Rels ty rel -> expr ty -> expr ty -> VProp
    | and : VProp -> VProp -> VProp
    | or  : VProp -> VProp -> VProp
    | not : VProp -> VProp
    (* TODO : add imply for guiding proofs *)
    .

    Fixpoint VPropDenote (vp : VProp) `{State _ v tyD} {st : StoreP str} : Prop :=
      match vp with
      | eq ty e1 e2       => evalE e1 = evalE e2
      | rel _ r _ e1 e2   => r (evalE e1) (evalE e2)
      | and vp1 vp2       => VPropDenote vp1 /\ VPropDenote vp2
      | or vp1 vp2        => VPropDenote vp1 \/ VPropDenote vp2
      | not vp'           => ~ (VPropDenote vp')
      end.
  End ParamV.

  (* TODO : remove spurious old code comments from commits on monotypecall *)

  Inductive Annotated v : Type :=
  | instruct  : statement v -> Annotated v
  | proc      : forall n (sc : Scope.type verse_type_system n),
      (forall w, Scope.allocation w sc -> (list (Annotated w)))
      -> Scope.allocation v sc -> Annotated v
  | annot     : VProp v       -> Annotated v
  .

  Definition AnnotatedCode v := list (Annotated v).

  Fixpoint denote1 v (ann : Annotated v) : line v (fun w => @mline _ w tyD)
    := match ann with
       | instruct _ s  => inst s
       | proc _ n sc p all => call (fun w wall =>
                                      map (denote1 _) (p w wall))
                                   all
       | annot _ p     => (inline
                             (fun state : State v tyD =>
                                (id,
                                 ((fun (st : StoreP str) => VPropDenote _ p (st := st)) : StoreP str -> Prop) : SPair str -> Prop)))
       end.

  Definition denote v (ann : AnnotatedCode v) : IntAnnotatedCode v tyD
    := map (denote1 v) ann.

End Annotated.

Arguments eq [tyD Rels v ty].
Arguments rel [tyD Rels v ty rel].
Arguments denote [tyD Rels v].

Global Infix "=" := (fun x y => eq (toExpr x) (toExpr y)) (at level 70) : annotation_scope.

Global Notation "X < R > Y" := (rel R X Y) (at level 99) : annotation_scope.
Global Infix "AND" := and (at level 56, left associativity) : annotation_scope.
Global Infix "OR"  := or  (at level 59, left associativity) : annotation_scope.

(* TODO : Somehow not being able to make this work without the 'WITH' *)
Notation "'CALL' f 'WITH' a"
  := ([ let sc := fst (Scope.inferNesting (Scope.Cookup.specialise f)) in
      proc _ _ _ _ sc
           (fun w => Scope.uncurryScope
                       (st := sc)
                       (f%function w))
           a ])
       (at level 60).

Notation "'CODE' l" := (map (@instruct _ _ _) l) (at level 60).
Notation "'ANNOT' a" := (map (@annot _ _ _) a)
                             (at level 60).

Arguments CUR [v k ty].
Arguments OLD [v k ty].
Arguments noRels {tyD}.
Arguments Annotated [tyD].
Arguments instruct [tyD Rels] {v}.
Arguments annot [tyD Rels] {v}.
