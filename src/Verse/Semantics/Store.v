Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.DecFacts.

Set Implicit Arguments.

Definition v_sig_eqb v (v_eqb : forall k (ty : type k) (v1 v2 : v _ ty), bool)
  : forall k1 k2 (ty1 : type k1) (ty2 : type k2), v _ ty1 -> v _ ty2 -> bool.
  intros k1 k2 ty1 ty2 var1 var2.
  destruct (kind_eq_dec k1 k2); [idtac | exact false].
  subst k2.
  destruct (ty_eq_dec ty1 ty2); [idtac | exact false].
  subst ty2.
  exact (v_eqb _ _ var1 var2).
Defined.

Record Store (tyD : typeC TypeDenote) :=
  {
    v : VariableT;
    v_eqb : forall {k} {ty : type k} (v1 v2 : v ty), bool;

    v_eqb_eq : forall {k} {ty : type k} (v1 v2 : v ty), v_eqb v1 v2 = true <-> v1 = v2;

    store : Type;
    eval  : store -> forall k {ty : type k} (var : v ty), typeDenote ty : Type;

    storeUpdate
    : forall k {ty : type k} (var : v ty)
             (f : @typeDenote TypeDenote _ _ ty -> @typeDenote TypeDenote _ _  ty),
        store -> store;

    evalUpdate
    : forall (s : store) k (ty : type k) (var : v ty) f,
        forall k' (ty' : type k') (v' : v ty'),
          (v_sig_eqb v (@v_eqb) _ _ v' var = false -> eval (storeUpdate var f s) v' = eval s v')
          /\
          eval (storeUpdate var f s) var = f (eval s var)
  }.

Arguments Store [tyD].
