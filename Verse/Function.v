Require Import Types.Internal.
Require Import Language.
Require Import String.
Require Import Ascii.
Require Import Fin.


Module Type Function.
  
  Parameter name    : string.

  Parameter np   :  nat.
  Parameter nl  : nat.
  Parameter param  : type -> Type.
  Parameter local  : type -> Type.

  Check sigT.
  
  Parameter porder : {o : Fin.t np -> {ty : type & (param ty)} & (forall p : { ty : type & (param ty) }, exists i : Fin.t np, o i = p)}.

  Parameter lorder : {o : Fin.t nl -> {ty : type & (local ty)} & (forall l : { ty : type & (local ty) }, exists i : Fin.t nl, o i = l)}.

  Inductive fvar : type -> Type :=
  | p : forall ty : type, param ty -> fvar ty
  | l : forall ty : type, local ty -> fvar ty
  .

  Parameter setup   : block fvar.

End Function.
