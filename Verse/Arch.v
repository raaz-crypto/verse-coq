Require Import String.
Require Import Verse.Types.Internal.

Module Type ARCH.

  (** Name of the architecture family *)

  Parameter name     : string.

  (** The registers for this architecture *)
  Parameter archvar  : type -> Type.


  (** The instruction mnemoics for this architecture *)
  Parameter mnemonic : (type -> Type) -> Type.

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

Module Type asm (A : ARCH).
  
  Import A.
  Definition assembly := list (mnemonic archvar).

  Parameter geninstr : (type -> Type) -> Type.

  Parameter translate : geninstr (archvar) -> option (mnemonic (archvar)).

End asm.