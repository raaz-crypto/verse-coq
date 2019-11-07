Require Import Verse.Error.
Require Import Verse.TypeSystem.

(** The universe of variables (of a given type system) *)
Definition U ts := forall k, TypeSystem.typeOf ts k -> Set.

Definition translate src tgt
           (tr : TypeSystem.translator src tgt)
           (v : U tgt) : U src
  := fun k ty => v k (Types.translate tr ty).

Arguments translate [src tgt] tr.
Definition result tgt (v : U tgt) : U (TypeSystem.result tgt)
    := fun k ty => match ty with
                | {- good -} => v k good
                | error _    => Empty_set
                end.

Arguments result [tgt].

Definition compile  src tgt
           (cr : TypeSystem.compiler src tgt)
           (v : U tgt) : U src
  := fun k ty => result v k (Types.compile cr ty).

Arguments compile [src tgt].
