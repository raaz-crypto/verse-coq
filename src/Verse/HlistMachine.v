(* begin hide *)
Require Import Verse.TypeSystem.
Require Import Verse.Scope.
Require Import Verse.Utils.hlist.
Require Import Verse.AbstractMachine.
Require Import Verse.Abstract.Machine.
(* end hide *)

Section Hlist.

  Context [ts : typeSystem] (sc : Scope.type ts).

  Variable tyD : typeDenote ts.

  Local Definition tyd ty := typeTrans tyD (projT2 ty).

  Definition memV : Variables.U ts := fun ty => member ty sc.

  Instance HlistMem : State memV tyD.
  refine {| str         := memory tyd sc;
            val         := fun m _ v => index v m;
            storeUpdate := fun _ v f m => update v m (f (index v m));
            evalUpdate  := _;
         |}.
  constructor.
  apply update_other_index.
  apply updated_index.
  Qed.

End Hlist.
