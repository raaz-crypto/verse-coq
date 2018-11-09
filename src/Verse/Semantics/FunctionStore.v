Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.DecFacts.
Require Import Verse.Semantics.Store.

Set Implicit Arguments.

Generalizable All Variables.

Section Context.

  Variable var : VariableT.
  Variable var_eqb : forall {k} {ty : type k} (v1 v2 : var ty), bool.

  Variable var_eqb_eq
    : forall {k} {ty : type k} (v1 v2 : var ty), var_eqb v1 v2 = true <-> v1 = v2.

  Definition contextUpdate (tyD : typeC TypeDenote)
             k {ty : type k} (v : var ty)
             (f : @typeDenote TypeDenote _ _ ty -> @typeDenote TypeDenote _ _ ty) :
    context var -> context var.
    unfold context in *. intros oldctxt k0 ty0 x.
    destruct (kind_eq_dec k0 k); subst.
    destruct (ty_eq_dec ty0 ty); subst.
    exact (if var_eqb x v then
             f (oldctxt _ _ x)               (* update according to f at var *)
           else
             oldctxt _ _ x).
    all: exact (oldctxt _ _ x).              (* use initial state value at all other points *)
  Defined.

  Axiom eq_eq_refl : forall A (a : A) (p : a = a), p = eq_refl.

  Lemma evalSane (tyD : typeC TypeDenote)
    : forall (s : context var) k (ty : type k) (v : var ty) f,
      forall k' (ty' : type k') (v' : var ty'),
        (v_sig_eqb var (@var_eqb) _ _ v' v = false -> (contextUpdate v f s) _ _ v' = s _ _ v')
        /\
        (contextUpdate v f s) _ _ v = f (s _ _ v).
    intros.
    constructor.
    unfold contextUpdate.
    unfold v_sig_eqb.
    intro.
    destruct (kind_eq_dec k' k).
    subst k'.
    unfold eq_rect_r.
    simpl in *.
    destruct (ty_eq_dec ty' ty).
    subst ty'.
    simpl in *.
    rewrite H.
    trivial.
    trivial.
    trivial.

    unfold contextUpdate.
    destruct (kind_eq_dec k k).
    pose (eq_eq_refl e).
    rewrite e0.
    unfold eq_rect_r.
    simpl.
    destruct (ty_eq_dec ty ty).
    pose (eq_eq_refl e1).
    subst e1.
    simpl.
    assert (var_eqb v v = true).

    apply (var_eqb_eq); trivial.
    rewrite H.
    trivial.
    contradict n; trivial.
    contradict n; trivial.
  Qed.

  Definition ctxtStore (tyD : typeC TypeDenote) : Store :=
    {| v := var;
       v_eqb := var_eqb;

       v_eqb_eq := var_eqb_eq;

       store := context var;

       eval  := id;
       storeUpdate := @contextUpdate tyD;

       evalUpdate := @evalSane tyD
    |}.

End Context.