(* begin hide *)
Require Import Verse.TypeSystem.
Require Import Verse.Scope.
Require Import Verse.Utils.hlist.
Require Import Verse.AbstractMachine.
Require Import Verse.Abstract.Machine.
(* end hide *)

Section Hlist.

  Context [ts : typeSystem] (sc : Scope.type ts).

  Variable tyD : typeDenote ts.

  Local Definition tyd ty := typeTrans tyD (projT2 ty).

  Definition memV : Variables.U ts := fun ty => member sc ty.

  (* Generic scoped code instantiated with `memV` *)
  Definition fillMemV [CODE : Variables.U ts -> Type]
             (genC : forall v, scoped v sc (CODE v)) :=
    uncurry (genC memV) (all_membership sc).

  Instance HlistMem : State memV tyD.
  refine {| str         := memory tyd sc;
            val         := fun m _ v => index v m;
            storeUpdate := fun _ v f m => update v m (f (index v m));
            evalUpdate  := _;
         |}.
  constructor.
  apply update_other_index.
  apply updated_index.
  Defined.

End Hlist.

Arguments fillMemV [ts sc CODE].

Require Import Verse.Language.Pretty.
Require Import Verse.AnnotatedCode.
Require Import Vector.
Import VectorNotations.
Require Import Verse.Language.Types.

Section CodeGen.

  Variable n : nat.
  Variable sc : Scope.type verse_type_system.

  Variable tyD : typeDenote verse_type_system.
  Variable Rels : forall (ty : typeOf verse_type_system direct),
      Rel tyD ty -> Prop
  .

  Variable ac : forall v, Scope.scoped v sc (AnnotatedCode tyD Rels v).

  Definition cp := interpret (denote (fillMemV ac)).

  (* We allow `getProp` to take a precondition to prefix to the
     extracted Prop. This is never exposed to the user, but is used in
     the CoarseAxiom to provide the proof of the procedure call
     specification to the main body proof.
   *)

  Definition getProp (pc : _ -> Prop)
             (ml : @mline _ (memV sc) tyD)
    := forall (st : str), pc st
                          ->
                          let (i,a) := (ml (HlistMem _ _)) in
                          a (st, st).

  Definition tpt := getProp (fun _ => True) cp.
(*
  Definition getProp (ml : @mline _ (Scope.scopeVar sc) tyD)
    := forall (st : str), snd (ml (scopeStore _ _))
                              ({| store := st |}, {| store := st |}).

  Definition tpt := getProp cp.
*)
End CodeGen.

Global Hint Unfold tpt : Wrapper.
Global Hint Unfold cp  : Wrapper.

Arguments cp sc [tyD].
Arguments getProp [sc tyD].
Arguments tpt sc [tyD Rels].

(* Extracting Prop object from annotated code *)

Ltac getProp func
  := (let cv := constr:(fun v => curry_vec (func v)) in
      let level0 := constr:(Scope.Cookup.specialise cv) in
      let level0break := (eval hnf in (Scope.inferNesting level0)) in
      let pvs := constr:(fst level0break) in
      let level1 := constr:(snd level0break) in
      let lvs := (eval hnf in (fst (Scope.inferNesting level1))) in
      exact (tpt (pvs ++ lvs)%list cv)).
