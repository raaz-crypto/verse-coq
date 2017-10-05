 Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Function.

  Variable var : varT.
  
  Record Function   := function
                         {
                           setup   : block var;
                           loop    : block var;
                           cleanup : block var;
                         }.

  Record FunVars   := funvars
                        {
                          fname   : string;
                          param   : list type;
                          local   : list type;
                        }.

  Inductive userTy : varT :=
  | inR ty : var ty -> userTy ty
  | onS ty : userTy ty
  .

  Definition userAlloc (local : list type) := allocation userTy local.

End Function.

Arguments inR [var ty] _.
Arguments onS [var] _.

Definition fscoped v p l := scoped v p (scoped v l (Function v)).

Definition func (reg : varT) (fv : FunVars) : Type := (forall (v : varT), fscoped v (param fv) (local fv)) * userAlloc reg (local fv).

