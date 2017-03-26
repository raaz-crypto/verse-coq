Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import Arch.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.


Fixpoint listSet {A : Type} (l : list A) : Ensemble A :=
  match l with
  | [] => Empty_set _
  | a :: lt => Ensembles.Add _ (listSet lt) a
  end.

Module Type Function (arch : ARCH).
  
  Parameter name     : string.

  (** The variable type on which the function body is parametrized *)
  Parameter fvar     : type -> Type.

  (** The ordered list of parameters of the function *)
  Parameter param    : list {ty : type & fvar ty}.

  (** Allocation onto _archvar_ from the local variables *)
  Parameter localloc : list {fv : {ty : type & fvar ty} & (arch.var (projT1 fv))}.

  Parameter loopvar  : {ty : type & fvar ty}.

  Definition local := map (@projT1 {ty : type & fvar ty} _) localloc.

  Parameter setup    : block fvar.
  Parameter loop     : block fvar.
  Parameter cleanup  : block fvar.

  Definition usedvars := Ensembles.Add _
                                       (Union _
                                              (Union _ (bvars setup) (bvars loop))
                                              (bvars cleanup))
                                       loopvar.

  (* ## Can be changed to use listSet and a disjoint union prop from the Ensemble library *)
  Parameter allUsedListed : forall v : (sigT fvar), Ensembles.In _ usedvars v ->
                                                    or (In v param) (In v local).
  
End Function.
