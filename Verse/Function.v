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

  Record FAllocation (pl lv rv : list type) (t : type) := fallocation
                          {
                            pa  : allocation v pl;
                            lva : allocation v lv;
                            lv  : v t;
                            rva : allocation v rv;
                          }.

  Definition fscoped (t : type) (pl lv rv : list type) (T : Type) := scoped v pl (scoped v lv (scoped v (t :: nil) (scoped v rv T))).

End Function.

Arguments name [v t] _ .
Arguments setup [v t] _ .
Arguments loop [v t] _ _ .
Arguments cleanup [v t] _ .

Arguments pa  [v pl lv rv t] _ .
Arguments lva [v pl lv rv t] _ .
Arguments lv  [v pl lv rv t] _ .
Arguments rva [v pl lv rv t] _ .

Definition func t pl lv rv := forall (v : varT),
                              scoped v pl (scoped v lv (scoped v rv (Function v t))).
