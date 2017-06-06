Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Types.Internal.
Require Import String.
Require Import List.
Import ListNotations.

Module Type ARCH.

  (** Name of the architecture family *)

  Parameter name     : string.

  (** The registers for this architecture *)

  Parameter register : varT.


  (** Encode the architecture specific restrictions on the instruction set **)

  Parameter wfinstr : instruction register -> Prop.

  (*

  Not need as of now.

  Fixpoint wfinstrB (b : block var) : Prop :=
    match b with
    | [] => True
    | i :: bt => and (wfinstr i) (wfinstrB bt)
    end.
   *)

  (** Generate code with assurance of well formedness **)

  
  Parameter callConv : forall paramTypes localTypes, allocation (machineVar register) (paramTypes ++ localTypes).

  (*

  Parameter generate : forall b : block var, wftypesB b -> wfvarB b -> wfinstrB b -> string.

   *)
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
