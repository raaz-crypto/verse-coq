Require Vector.
Require Import String.
Require Import Verse.Types.

(** An argument for an instruction *)

Inductive op :=
| Add    | Mul    | Div    | Rem | Sub
| BitOr  | BitAnd | BitXOR | BitComp
.


Section Instruction.

  (** The register type used in the instruction set *)
  Variable r : forall {kp : kind}, type kp -> Type. Arguments r {kp} _.

  (** The operands of the instruction set *)
  Inductive operand : forall {k : kind}, type k -> Type :=
  | param    {k : kind}{t : type k}  : operand t
  | stack    {k : kind}{t : type k}  : operand t
  | register {k : kind}{t : type k}  : r t -> operand t
  | atIndex  {n : nat}{e : endian}{t : type value}(i  : nat) :
      (i < n) -> operand (array n e t).

  Inductive instruction : Type :=
  | initialize {t : type value} : operand t -> constant t -> instruction
  | copy       {t : type value} : operand t -> operand t  -> instruction
  | update     {t : type value}
    : op -> operand t -> operand t -> instruction
  (** x = x op y *)
  | assign     {t : valuetype}
    : op -> operand t -> operand t -> operand t -> instruction
  (** x = y op z *)
  .

End Instruction.

Print instruction.

Module Type ARCH.
  (** Name of the architecture *)
  Parameter name : string.
  (** The type that captures registers of the architecture *)
  Parameter reg  : forall (k : kind), type k -> Type.

  (** The proposition that determines whether a given register is
  supported or not of a given register *)
  Parameter regSupport : forall {k : kind}{t : type k}, reg k t -> Prop.

  Parameter instructionSupport : instruction reg -> Prop.

End ARCH.
