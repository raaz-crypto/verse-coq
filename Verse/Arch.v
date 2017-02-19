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
  Parameter archvar  : varT.


  (** Encode the architecture specific restrictions on the instruction set **)

  Parameter wfinstr : instruction archvar -> Prop.

  Fixpoint wfinstrB (b : block archvar) : Prop :=
    match b with
    | [] => True
    | i :: bt => and (wfinstr i) (wfinstrB bt)
    end.

  (** Generate code with assurance of well formedness **)

  Parameter callConv : forall {var} (lvar : list (sigT var)) v, In v lvar ->  archvar (projT1 v).
   
  Parameter generate : forall b : block archvar, wftypesB b -> wfvarB b -> wfinstrB b -> string.
  
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

