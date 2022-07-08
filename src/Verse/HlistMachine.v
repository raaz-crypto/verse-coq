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

  Definition memV : Variables.U ts := fun ty => member sc ty.

  (* Generic scoped code instantiated with `memV` *)
  Definition fillMemV [CODE : Variables.U ts -> Type]
             (genC : forall v, scoped v sc (CODE v)) :=
    uncurry (genC memV) (all_membership sc).

  Instance HlistMem : State memV tyD.
  refine {| str         := memory tyd sc;
            val         := fun m _ v => index v m;
            storeUpdate := fun _ v f m => update v m (f (index v m));
            evalUpdate  := _;
         |}.
  constructor.
  apply update_other_index.
  apply updated_index.
  Defined.

End Hlist.

Arguments fillMemV [ts sc CODE].
