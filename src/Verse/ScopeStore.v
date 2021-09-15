Require Import Verse.TypeSystem.
Require Import Verse.Language.
Require Verse.Scope.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.Semantics.

Require Import Eqdep_dec.
Require Import Equality.

Require Import Vector.
Import VectorNotations.

Section ScopeStore.

  Variable ts : typeSystem.
  Variable tyD : typeDenote ts.

  Local Definition tyd  := typeTrans tyD.
  Arguments tyd [k].

  Local Definition type := typeOf ts.

  Definition scstr {n} (sc : Scope.type ts n)
    := Scope.allocation tyd sc.

  Fixpoint frmStore
           {n} {sc : Scope.type ts n} (s : scstr sc)
           {k} {ty : type k} (x : Scope.scopeVar sc _ ty)
    : tyd ty
    :=
      match x in Scope.scopeVar sc0 _ ty0 return scstr sc0
                                                 -> (tyd ty0 : Type) with
      | Scope.headVar    => fun s0 => let '(vx, _) := s0 in vx
      | Scope.restVar rx => fun s0 => let '(_, st) := s0 in frmStore st rx
      end s.

Fixpoint wrtStore
         {n} {sc : Scope.type ts n}
         {k} {ty : type k} (var : Scope.scopeVar sc _ ty)
  : (tyd ty -> tyd ty) ->
    scstr sc -> scstr sc :=
  match var as var0 in Scope.scopeVar sc0 _ ty0 return
        (tyd ty0 -> tyd ty0)
        -> scstr sc0 -> scstr sc0
  with
  | Scope.headVar    => fun f s => let '(vx, st) := s in (f vx, st)
  | Scope.restVar rx => fun f s => let '(vx, st) := s in (vx, wrtStore rx f st)
  end.

(** TODO : Needs a proof eventually! *)
Axiom frmWrt :
  forall n (sc : Scope.type ts n)
           (st : scstr sc)
           k (ty : type k) (var : Scope.scopeVar sc _ ty) f
           k' (ty' : type k') (v' : Scope.scopeVar sc _ ty'),
    ( ~ eq_dep2 var v'-> frmStore (wrtStore var f st) v' = frmStore st v')
    /\
    frmStore (wrtStore var f st) var = f (frmStore st var).

Instance scopeStore
           n (sc : Scope.type ts n)
  : State (Scope.scopeVar sc) tyD :=
  {| str   := scstr sc;

     val := @frmStore n sc;

     storeUpdate := @wrtStore _ sc;

     evalUpdate := @frmWrt _ sc;
  |}.

End ScopeStore.

Arguments scstr [ts] _ [n] _.
Arguments frmStore [ts tyD n sc] {_} [k ty].
Arguments wrtStore [ts tyD n sc k ty].
Arguments scopeStore [ts] _ [n].

Require Import Verse.AnnotatedCode.
Require Import Vector.
Import VectorNotations.
Require Import Verse.Language.Types.

Section CodeGen.

  Variable n : nat.
  Variable sc : Scope.type verse_type_system n.

  Variable tyD : typeDenote verse_type_system.
  Variable Rels : forall (ty : typeOf verse_type_system direct),
      Rel tyD ty -> Prop
  .

  Variable ac : forall v, Scope.scoped v sc (AnnotatedCode tyD Rels v).

  Definition cp := interpret (denote (Scope.fillScoped ac)).

  (* We allow `getProp` to take a precondition to prefix to the
     extracted Prop. This is never exposed to the user, but is used in
     the CoarseAxiom to provide the proof of the procedure call
     specification to the main body proof.
   *)

  Definition getProp (pc : _ -> Prop)
             (ml : @mline _ (Scope.scopeVar sc) tyD)
    := forall (st : str), pc st
                          ->
                          snd (ml (scopeStore _ _))
                              (st, st).

  Definition tpt := getProp (fun _ => True) cp.
(*
  Definition getProp (ml : @mline _ (Scope.scopeVar sc) tyD)
    := forall (st : str), snd (ml (scopeStore _ _))
                              ({| store := st |}, {| store := st |}).

  Definition tpt := getProp cp.
*)
End CodeGen.

Arguments cp [n] sc [tyD].
Arguments getProp [n sc tyD].
Arguments tpt [n] sc [tyD Rels].

(* Extracting Prop object from annotated code *)

Ltac getProp func
  := (let level0 := constr:(Scope.Cookup.specialise func) in
      let level0break := (eval hnf in (Scope.inferNesting level0)) in
      let pvs := constr:(fst level0break) in
      let level1 := constr:(snd level0break) in
      let lvs := (eval hnf in (fst (Scope.inferNesting level1))) in
      exact (tpt (pvs ++ lvs) func)).
