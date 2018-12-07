Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.DecFacts.
Require Import Verse.Semantics.Store.

Require Import Eqdep_dec.
Require Import Equality.

Require Import Vector.
Import VectorNotations.

Set Implicit Arguments.

Generalizable All Variables.

Fixpoint frmStore (tyd : VariableT)
         `{vT : Vector.t (some type) n} (s : allocation tyd vT)
         `{ty : type k} (x : scopeVar vT ty)
  : (tyd _ ty : Type) :=
  match x in scopeVar vT0 ty0 return (allocation tyd vT0)
                                     -> (tyd _ ty0 : Type) with
  | headVar    => fun s0 => let '(vx, _) := s0 in vx
  | restVar rx => fun s0 => let '(_, st) := s0 in frmStore _ st rx
  end s.

Fixpoint wrtStore (tyd : VariableT)
         `(vT : Vector.t (some type) n)
         `{ty : type k} (var : scopeVar vT ty)
  : ((tyd _ ty : Type) -> (tyd _ ty : Type)) ->
    allocation tyd vT -> allocation tyd vT :=
  match var as var0 in scopeVar vT0 ty0 return
        ((tyd _ ty0 : Type)
         -> tyd _ ty0 : Type)
        -> allocation tyd vT0 -> allocation tyd vT0
  with
  | headVar    => fun f s => let '(vx, st) := s in (f vx, st)
  | restVar rx => fun f s => let '(vx, st) := s in (vx, wrtStore _ rx f st)
  end.


Fixpoint frmWrt (tyd : VariableT)
         `(vT : Vector.t (some type) n)
         (s : allocation tyd vT) k (ty : type k) (v : scopeVar vT ty) f {struct vT} :
  forall k' (ty' : type k') (v' : scopeVar vT ty'),
    (v_sig_eqb _ (@scopeVar_eqb _ vT) _ _ v' v = false ->
     frmStore tyd (wrtStore tyd v f s) v' = frmStore tyd s v')
    /\
    frmStore tyd (wrtStore tyd v f s) v = f (frmStore tyd s v).
  intros.
  constructor.
  intro.
  dependent induction v; dependent destruction v'.
  destruct s.
  contradict H.
  unfold v_sig_eqb.
  destruct (kind_eq_dec (projT1 (hd v)) (projT1 (hd v))).
  pose (eq_proofs_unicity (eq_dec_eq_dec_P kind_eq_dec) e eq_refl).
  subst e.
  simpl.
  destruct (ty_eq_dec (projT2 (hd v)) (projT2 (hd v))).
  pose (eq_proofs_unicity (eq_dec_eq_dec_P ty_eq_dec) e eq_refl).
  subst e.
  simpl.
  unfold scopeVar_eqb.
  simpl.
  congruence.
  congruence.
  congruence.

  destruct s.
  trivial.

  destruct s.
  trivial.

  destruct s.
  apply IHv.
  unfold v_sig_eqb in *.
  destruct (kind_eq_dec k0 k).
  subst k0.
  simpl in *.
  destruct (ty_eq_dec ty0 ty).
  subst ty0.
  simpl in *.
  unfold scopeVar_eqb in *.
  simpl idxInScope in H.
  destruct (PeanoNat.Nat.eq_dec (S (idxInScope v')) (S (idxInScope v0))).
  contradict H; discriminate.
  destruct (PeanoNat.Nat.eq_dec (idxInScope v') (idxInScope v0)).
  contradict n.
  apply eq_S; trivial.
  trivial.
  trivial.
  trivial.

    intros.
  dependent induction v.
  destruct s; trivial.

  destruct s.
  simpl.
  apply (IHv _ _ k ty v0).
Qed.


Section Store.

  Variable n : nat.
  Variable vT : Vector.t (some type) n.

  Definition scopeStore (tyD : typeC TypeDenote) : Store :=
    {| v := scopeVar vT;
       v_eqb := @scopeVar_eqb _ vT;

       v_eqb_eq := @scopeVar_eqb_eq _ vT;

       store := allocation (fun _ => typeDenote) vT;

       eval := frmStore (fun _ => typeDenote);
       storeUpdate := @wrtStore (fun _ => typeDenote) _ vT;

       evalUpdate := @frmWrt (fun _ => typeDenote) _ vT
    |}.

End Store.

Arguments scopeStore [n] _ [tyD].
