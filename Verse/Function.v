 Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.


Section Function.

  Variable v : varT.
  
  Record Function t := function
                         {
                           name    : string;
                           setup   : block v;
                           loop    : v t -> block v;
                           cleanup : block v;
                         }.

  Record FunVars   := funvars
                         {
                           param   : list type;
                           local   : list type;
                         }.

  Definition fscoped (t : type) (pl lv rv : list type) (T : Type) := scoped v pl (scoped v lv (scoped v (t :: nil) (scoped v rv T))).

End Function.

Arguments name [v t] _ .
Arguments setup [v t] _ .
Arguments loop [v t] _ _ .
Arguments cleanup [v t] _ .

Definition func t pl lv rv := forall (v : varT),
                              scoped v pl (scoped v lv (scoped v rv (Function v t))).
