 Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.


Section Function.

  Variable v : varT.
  
  Record Function   := function
                         {
                           name    : string;
                           setup   : block v;
                           loop    : block v;
                           cleanup : block v;
                         }.

  Record FunVars   := funvars
                         {
                           param   : list type;
                           local   : list type;
                         }.

  Definition fscoped (p l : list type) (T : Type) := scoped v p (scoped v l T).

End Function.

Arguments name [v] _ .
Arguments setup [v] _ .
Arguments loop [v] _ .
Arguments cleanup [v] _ .

Definition func p l := forall (v : varT),
                              scoped v p (scoped v l (Function v)).
