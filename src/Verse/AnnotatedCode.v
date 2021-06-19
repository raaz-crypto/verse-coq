Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Ast.
Require Import Verse.Language.Pretty.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.PList.

Require Import EqdepFacts.
Import EqNotations.

Declare Scope annotation_scope.
Delimit Scope annotation_scope with annot.

Section Annotated.

  Variable v : Variables.U verse_type_system.
  Arguments v [k].

  Inductive dv : Variables.U verse_type_system :=
  | NEW k ty :> v ty -> dv k ty
  | OLD k ty : v ty -> dv k ty
  .

  Arguments NEW [k ty].
  Arguments OLD [k ty].

  Global Instance v_to_expdv ty : EXPR dv ty (v ty)
    := { toExpr := fun t => valueOf (var (NEW t)) }.

  Definition expr  T := Ast.expr  dv T.
  Definition lexpr T := Ast.lexpr dv T.

  Variable tyD : typeDenote verse_type_system.

  Definition leval {T} (l : lexpr T) `{State _ v tyD} {st : StoreP str}
    : typeTrans tyD T
    := let val2 {k} {ty} (x : dv k ty) := match x with
                                          | NEW x => VAL x
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


  Definition Rel (ty : typeOf verse_type_system direct)
    := typeTrans tyD ty -> typeTrans tyD ty -> Prop.

  Variable Rels : forall (ty : typeOf verse_type_system direct),
      Rel ty -> Prop
  .

  Inductive noRels : forall (ty : typeOf verse_type_system direct),
      Rel ty -> Type :=
  .

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

  Inductive Annotated : Type :=
  | inst  : statement v -> Annotated
  | annot : VProp       -> Annotated
  .

  Definition AnnotatedCode := list Annotated.

  Definition denote (ann : AnnotatedCode) : IntAnnotatedCode v tyD
    :=  fun _ => (map (fun a =>
                         (match a with
                          | inst s  => instruct s
                          | annot p => (inline (id , ((fun (st : StoreP str) => VPropDenote p (st := st)) : StoreP str -> Prop) : SPair str -> Prop))
                          end) : line _ mline))
                   ann
  .

End Annotated.

Arguments eq [v tyD Rels ty].
Arguments rel [v tyD Rels ty rel].

Global Infix "=" := (fun x y => eq (toExpr x) (toExpr y)) (at level 70) : annotation_scope.

Global Notation "X < R > Y" := (rel R X Y) (at level 99) : annotation_scope.
Global Infix "AND" := and (at level 56, left associativity) : annotation_scope.
Global Infix "OR"  := or  (at level 59, left associativity) : annotation_scope.

Notation "'CODE' l" := (map (@instruct _ _ _) l) (at level 60).
Notation "'ANNOT' a" := (map (@annot _ _ _) a)
                             (at level 60).

Arguments NEW [v k ty].
Arguments OLD [v k ty].
Arguments noRels {tyD}.
Arguments Annotated v [tyD].
Arguments inst [v tyD] {Rels}.
Arguments annot [v tyD] {Rels}.
