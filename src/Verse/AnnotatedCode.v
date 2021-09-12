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
    | nil : VProp
    | eq  : forall ty, expr ty -> expr ty -> VProp
    | rel : forall ty rel, Rels ty rel -> expr ty -> expr ty -> VProp
    | and : VProp -> VProp -> VProp
    | or  : VProp -> VProp -> VProp
    | not : VProp -> VProp
    (* TODO : add imply for guiding proofs *)
    .

    Fixpoint VPropDenote (vp : VProp) `{State _ v tyD} {st : StoreP str} : Prop :=
      match vp with
      | nil               => True
      | eq ty e1 e2       => evalE e1 = evalE e2
      | rel _ r _ e1 e2   => r (evalE e1) (evalE e2)
      | and vp1 vp2       => VPropDenote vp1 /\ VPropDenote vp2
      | or vp1 vp2        => VPropDenote vp1 \/ VPropDenote vp2
      | not vp'           => ~ (VPropDenote vp')
      end.
  End ParamV.

End Annotated.
  (* TODO : remove spurious old code comments from commits on monotypecall *)

Record specified tyD Rels v T := { preC : VProp tyD Rels v;
                                   block : T tyD Rels v;
                                   postC : VProp tyD Rels v
                                 }.

Inductive Annotated tyD Rels v : Type :=
| instruct  : statement v -> Annotated tyD Rels v
| proc      : forall n ty, (forall w,
                               Scope.allocation w (Scope.const n ty)
                               -> specified tyD Rels w
                                            (fun a b c => list (Annotated a b c)))
                           -> Scope.allocation v (Scope.const n ty)
                           -> Annotated tyD Rels v
| annot     : VProp tyD Rels v       -> Annotated tyD Rels v
.

Definition specifiedC tyD Rels n ty
  := (forall w,
         Scope.allocation w (Scope.const n ty)
         -> specified tyD Rels w
                      (fun a b c => list (Annotated a b c))).
(*specified tyD Rels v
                                               (fun a b c => list (Annotated a b c)).*)

Definition AnnotatedCode tyD Rels v := list (Annotated tyD Rels v).

Fixpoint denote1 tyD Rels v
         (ann : Annotated tyD Rels v) {struct ann}
  : line v (fun w => @mline _ w tyD)
  :=
    let anndenote [x] p := (inline
                              (fun state : State x tyD =>
                                 (id,
                                  ((fun (st : StoreP str) => VPropDenote _ _ _ p (st := st)) : StoreP str -> Prop) : Pair str -> Prop))) in
    match ann with
    | instruct _ _ _ s  => inst s
    | annot _ _ _ p     => anndenote p
    | proc _ _ _ n _ p all => call (fun w wall =>
                                      let (pre, bl, post) := p w wall in
                                      anndenote pre ::
                                                map (denote1 _ _ _) bl
                                                ++ [anndenote post])
                                   all
    end.

Definition denote tyD Rels v (ann : AnnotatedCode tyD Rels v)
  : IntAnnotatedCode v tyD
  := map (denote1 tyD Rels v) ann.

Arguments eq [tyD Rels v ty].
Arguments and [tyD Rels v].
Arguments or [tyD Rels v].
Arguments rel [tyD Rels v ty rel].
Arguments VPropDenote [tyD Rels v].
Arguments denote [tyD Rels v] : simpl never.

Global Infix "=" := (fun x y => eq (toExpr x) (toExpr y)) (at level 70) : annotation_scope.

Global Notation "X < R > Y" := (rel R X Y) (at level 99) : annotation_scope.
Global Infix "VAND" := and (at level 56, left associativity) : annotation_scope.
Global Infix "VOR"  := or  (at level 59, left associativity) : annotation_scope.


(* TODO : Somehow not being able to make this work without the 'WITH' *)
(* The implicit parameters of `proc` to do with its scope seem to be
   inferable in the monotype call setting!
 *)

Notation "'CALL' f 'WITH' a"
  := ([ let sc := fst (Scope.inferNesting (Scope.Cookup.specialise f)) in
      proc _ _ _ _ (*(Scope.nesting (Scope.Cookup.specialise f))*) _ (*(projT1 (fst sc))*)
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
Arguments proc [tyD Rels v n ty].
Arguments annot [tyD Rels] {v}.
Arguments nil {tyD Rels v}.

Notation "F 'DOES' Post" := ({| preC := nil ; block := F; postC := Post |})
(at level 60).

(*
Notation "'SPEC' { Pre } F { Post }" := ({| preC := Pre; block := F; postC := Post |}).
*)
