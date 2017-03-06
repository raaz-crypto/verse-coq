Require Import Types.Internal.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.


Fixpoint listSet {A : Type} (l : list A) : Ensemble A :=
  match l with
  | [] => Empty_set _
  | a :: lt => Ensembles.Add _ (listSet lt) a
  end.

Module Type Function.
  
  Parameter name    : string.

  Parameter param  : type -> Type.
  Parameter local  : type -> Type.

  Inductive fvar : type -> Type :=
  | p : forall ty : type, param ty -> fvar ty
  | l : forall ty : type, local ty -> fvar ty
  .

  Parameter paramord : list (sigT param).
  Parameter localord : list (sigT local).
  Parameter loopvar  : sigT local.

  Parameter setup   : block fvar.
  Parameter loop    : block fvar.
  Parameter cleanup : block fvar.

  Definition usedvars := Ensembles.Add _ (Union _ (Union _ (getvars setup) (getvars cleanup)) (getvars cleanup)) (existT _ _ (l _ (projT2 loopvar))).
  
  Parameter allUsedListed : forall v : (sigT fvar), Ensembles.In _ usedvars v ->
                                                      match v with
                                                      | existT _ _ (p _ pv) => In (existT _ _ pv) paramord
                                                      | existT _ _ (l _ lv) => In (existT _ _ lv) localord
                                                      end.
End Function.
