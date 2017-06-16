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
                           setup   : block v;
                           loop    : v t -> block v;
                           cleanup : block v;
                         }.

  Record FAllocation (pl lv rv : list type) (t : type) := fallocation
                          {
                            pa  : allocation v pl;
                            lva : allocation v lv;
                            loopvar : v t;
                            rva : allocation v rv;
                          }.

  Definition fscoped (t : type) (pl lv rv : list type) (T : Type) := scoped v pl (scoped v lv (scoped v (t :: nil) (scoped v rv T))).

End Function.

Definition func t pl lv rv := forall (v : varT),
                              scoped v pl (scoped v lv (scoped v rv (Function v t))).
