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

  (** The variables associated with the  set *)
  Inductive var : forall {k : kind}, type k -> Type :=
  | param    {k : kind}{t : type k}  : var t
  | stack    {k : kind}{t : type k}  : var t
  | register {k : kind}{t : type k}  : r t -> var t
  | atIndex  {n : nat}{e : endian}{t : type value}(i  : nat) :
      (i < n) -> var (array n e t).

  (** The arguments for the instruction *)
  Inductive arg : forall {k : kind}, type k -> Type :=
  | variable {k : kind}{t : type k}: var t -> arg t
  | immediate {t : type value} : constant t -> arg t.

  Inductive instruction : Type :=
  | initialise     {t : type value} : var t -> arg t  -> instruction
  | update     {t : type value}
    : op -> var t -> arg t -> instruction
  (** x = x op y *)
  | assign     {t : valuetype}
    : op -> var t -> arg t -> arg t -> instruction
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
