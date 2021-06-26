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
  Variable v : Variables.U ts.
  Variable tyD : typeDenote ts.

  Local Definition tyd  := typeTrans tyD.
  Arguments tyd [k].

  Definition type := typeOf ts.

  Definition scstr {n} (sc : Scope.type ts n)
    := Scope.allocation tyd sc.

  Fixpoint frmStore
           {n} {sc : Scope.type ts n} (s : Store (scstr sc))
           {k} {ty : type k} (x : Scope.scopeVar sc _ ty)
    : tyd ty
    :=
      match x in Scope.scopeVar sc0 _ ty0 return scstr sc0
                                                 -> (tyd ty0 : Type) with
      | Scope.headVar    => fun s0 => let '(vx, _) := s0 in vx
      | Scope.restVar rx => fun s0 => let '(_, st) := s0 in frmStore {| store := st |} rx
      end store.

Fixpoint wrtStore
         {n} {sc : Scope.type ts n}
         {k} {ty : type k} (var : Scope.scopeVar sc _ ty)
  : (tyd ty -> tyd ty) ->
    Store (scstr sc) -> Store (scstr sc) :=
  match var as var0 in Scope.scopeVar sc0 _ ty0 return
        (tyd ty0 -> tyd ty0)
        -> Store (scstr sc0) -> Store (scstr sc0)
  with
  | Scope.headVar    => fun f s => let '(vx, st) := store in {| store := (f vx, st) |}
  | Scope.restVar rx => fun f s => let '(vx, st) := store in {| store := (vx, store (Store := wrtStore rx f {| store := st |})) |}
  end.

(** TODO : Needs a proof eventually! *)
Axiom frmWrt :
  forall n (sc : Scope.type ts n)
           (st : Store (scstr sc))
           k (ty : type k) (var : Scope.scopeVar sc _ ty) f
           k' (ty' : type k') (v' : Scope.scopeVar sc _ ty'),
    ( ~ eq_dep2 var v'-> frmStore (wrtStore var f st) v' = frmStore st v')
    /\
    frmStore (wrtStore var f st) var = f (frmStore st var).

Instance scopeStore
           n (sc : Scope.type ts n)
  : State (Scope.scopeVar sc) tyD :=
  {| str   := _;

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

  Definition asc
    := Vector.map (fun sty => let 'existT _ _ ty := sty in
                              existT _ _ (typeTrans tyD ty))
                  sc.

  Variable ac : forall v, Scope.scoped v sc (AnnotatedCode v tyD Rels).

  Definition c := denote _ _ _ (Scope.fillScoped ac) (scopeStore _ _).

  Definition cp := linesDenote _ _ store_semantics c.

  Definition tpt := forall (st : str), snd cp
                                           ({| store := st |}, {| store := st |}).

End CodeGen.

Arguments cp [n] sc [tyD].
Arguments tpt [n] sc [tyD Rels].

(* Extracting Prop object from annotated code *)

Ltac getProp func
  := (let level0 := constr:(Scope.Cookup.specialise func) in
      let level0break := (eval hnf in (Scope.inferNesting level0)) in
      let pvs := constr:(fst level0break) in
      let level1 := constr:(snd level0break) in
      let lvs := (eval hnf in (fst (Scope.inferNesting level1))) in
      exact (tpt (pvs ++ lvs) func)).
