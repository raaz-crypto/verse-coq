Require Import Verse.TypeSystem.
Require Import Verse.Language.Pretty.
Require Import Verse.Language.Types.
Require Import Verse.Ast.
Require Scope.
Require Import Verse.Monoid.
Require Import Verse.HlistMachine.

Require Import List.
Import List.ListNotations.

Section AnnotatedCode.

  Variable tyD : typeDenote verse_type_system.

  Definition Str v := Variables.renaming v tyD.

  (* We need the pair of stores an annotation references to be wrapped
  into a typeclass to provide notations for annotations
   *)
  Definition Pair A : Type := A * A.
  Class StoreP str := { oldAndNew : Pair str }.

  Coercion Build_StoreP : Pair >-> StoreP.

  Definition ann v := StoreP (Str v) -> Prop.

  Inductive line (v : Variables.U verse_type_system) :=
  | inst      : statement v -> line v
  | annot     : ann v -> line v
  .

  Definition lines v := list (line v).

  Definition lineDenote [sc] (l : line (HlistMachine.variable sc))
    : mline sc tyD
    := match l with
       | inst _ s   => justInst (Internals.denoteStmt _ _ _ s)
       | annot _ a => justAssert (fun sp => a ((val (fst sp), val (snd sp)) : Pair _))
       end.

  Definition linesDenote [sc] (ls : lines (HlistMachine.variable sc))
    := mapMconcat (@lineDenote _) ls.

  Definition codeDenote sc (ls : forall v, Scope.scoped v sc (lines v))
    : mline sc tyD
    := let sls := HlistMachine.specialise sc ls in linesDenote sls.

End AnnotatedCode.

Arguments inst [tyD v].
Arguments annot [tyD v].
Arguments lineDenote [tyD sc].
Arguments linesDenote [tyD sc].
Arguments codeDenote [tyD sc].

(* Mapping instances for custom syntax notations *)

#[export] Instance statement_line tyD (v : VariableT) : AST_maps (list (statement v)) (line tyD v)
  := {|
    CODE := List.map (@inst _ _)
  |}.

#[export] Instance ann_line tyD (v : VariableT) : AST_maps (ann tyD v) (line tyD v)
  := {| CODE := fun an => [ annot an ] |}.


(*Notation "'CODE' c" := (List.map (@inst _ _) c) (at level 58).*)
(* Notations for annotations *)

Notation "'INIT' v" := (fst (oldAndNew (str := Str _ _)) _ v) (at level 50).
(* TODO - VAL level has to be changed to be stronger than that of '='
          and of b itvector arithmetic notations *)
Notation "'VAL' v" := (snd (oldAndNew (str := Str _ _)) _ v) (at level 50).

Notation "'ASSERT' P" := (CODE ((fun _ : StoreP (Str _ _) => P) : ann _ _)) (at level 100).

Require Import Verse.Scope.
Section CodeGen.

  Variable sc : Scope.type verse_type_system.

  Variable tyD : typeDenote verse_type_system.

  Variable ac : forall v, Scope.scoped v sc (lines tyD v).

  Definition cp := codeDenote ac.

  (* We allow `getProp` to take a precondition to prefix to the
     extracted Prop. This is never exposed to the user, but is used in
     the CoarseAxiom to provide the proof of the procedure call
     specification to the main body proof.
   *)

  Definition getProp (pc : _ -> Prop)
             (ml : mline sc tyD)
    := forall (st : HlistMachine.state sc tyD), pc st
                          ->
                          let (i,a) := ml in
                          a (st, st).

  (* Note that getProp acts on `mline`s and the setoid equivalence for
  `mline` is not the Leibniz equality. We frequently prefer to do
  rewrites with monoidal laws inside a `getProp` and prove those
  resulting conditions. The following provides the facility for the
  same.
  *)
  Global Add Parametric Morphism pc : (getProp pc) with signature
      (SetoidClass.equiv ==> Basics.flip Basics.impl) as getProper.
  Proof.
    destruct x, y.
    unfold Basics.impl.
    intro mlEq.
    destruct mlEq as [iEq aEq].
    rewrite iEq.
    unfold getProp.
    intros P0 st pcst.
    now apply aEq, P0.
  Defined.

  Definition tpt := getProp (fun _ => True) cp.

End CodeGen.

Global Hint Unfold tpt : Wrapper.
Global Hint Unfold cp  : Wrapper.

Arguments cp sc [tyD].
Arguments getProp [sc tyD].
Arguments tpt sc [tyD].



(* Extracting Prop object from annotated code *)

Ltac getProp func
  := (let cv := constr:(fun v => curry_vec (func v)) in
      let level0 := constr:(Scope.Cookup.specialise cv) in
      let level0break := (eval hnf in (Scope.inferNesting level0)) in
      let pvs := constr:(fst level0break) in
      let level1 := constr:(snd level0break) in
      let lvs := (eval hnf in (fst (Scope.inferNesting level1))) in
      exact (tpt (pvs ++ lvs)%list cv)).
