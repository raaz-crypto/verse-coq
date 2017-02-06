Require Import Verse.Language.
Require Import String.
Require Import Verse.Types.Internal.
Require Import List.
Import ListNotations.

Module Type ARCH.

  (** Name of the architecture family *)

  Parameter name     : string.

  (** The registers for this architecture *)
  Parameter archvar  : type -> Type.


  (** Encode the architecture specific restrictions on the instruction set **)

  Parameter wfinstr : instruction archvar -> Prop.

  Fixpoint wfinstrb (b : block archvar) : Prop :=
    match b with
    | [] => True
    | i :: bt => and (wfinstr i) (wfinstrb bt)
    end.

  (** Generate code with assurance of well formedness **)

  Parameter callConv : forall (var : type -> Type) (lvar : list (sigT var)) (v : sigT var), In v lvar ->  (forall ty : type, var ty -> option (archvar ty)).
   
  Parameter generate : forall b : block archvar, wftypesb b -> wfvarb b -> wfinstrb b -> string.
  
  (**

    Translate the assignment statement to assembly. Certain assignment
    instructions can fail, for example a three address assignment like
    [A <= B + C] is not supported on a 2-address machine like x86. and
    hence the result of a translation is a [option (list mnemonic)]
    instead of just a [list mnemonics].

   *)

  (** Convert the loop statement in assembly instruction. *)
  (*Parameter loop
  : forall {b : bound}{ty : type (Bounded b)},
      var reg ty -> arg reg ty -> list mnemonic -> list mnemonic.*)

End ARCH.

