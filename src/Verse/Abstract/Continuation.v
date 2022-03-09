Require Import Verse.Utils.hlist.

Section ContMachine.
  Context {sort : Type}(A : sort -> Type).
  Definition cont (ss : list sort) := forall B : Type, curried A B ss -> B.
  Definition transform (ins outs : list sort) := cont outs -> cont ins.
  Definition idTrans {ins : list sort} : transform ins ins := fun x => x.
End ContMachine.

Arguments idTrans {sort A ins}.
Definition seq {sort : Type}{ins mid outs : list sort} {A : sort -> Type} (tr0 : transform A ins mid) (tr1 : transform A mid outs)
             : transform A ins outs
    := fun cont => tr0 (tr1 cont).


Arguments seq {sort} {ins mid outs}{A}.
Check seq.
Notation "[seq| tr0 ; tr1 |]"  := (seq tr0 tr1).
Notation "[seq| tr0 ; .. ; trn1 ; trn |]" := (seq tr0 .. (seq trn1 trn) ..).
Print idTrans.
Definition nota {sort}{ins mid outs : list sort} {A}
           (tr0 : transform A ins mid) (tr1 : transform A mid outs) :
             transform A ins outs := [seq| tr0 ; tr1 ; idTrans |].
