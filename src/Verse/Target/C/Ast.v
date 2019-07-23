Require Verse.TypeSystem.
Require Verse.Nibble.
Require Verse.Error.
Set Implicit Arguments.

(*

The type system for the target C. Note that we only capture a subset
of possible types of C as this is the only type that is relevant for
us when compiling verse code.

*)

Inductive type : TypeSystem.kind -> Type :=
| uint8_t  : type TypeSystem.direct
| uint16_t : type TypeSystem.direct
| uint32_t : type TypeSystem.direct
| uint64_t : type TypeSystem.direct
| array      : nat -> type TypeSystem.direct    -> type TypeSystem.memory
| ptrToArray : nat -> type TypeSystem.direct    -> type TypeSystem.memory
.



Definition const (t : type TypeSystem.direct) :=
  match t with
  | uint8_t  => Nibble.bytes 1
  | uint16_t => Nibble.bytes 2
  | uint32_t => Nibble.bytes 4
  | uint64_t => Nibble.bytes 8
  end.

Definition index (t : type TypeSystem.memory) := nat.

Definition contentType (t : type TypeSystem.memory) :=
  match t with
  | array _ ty => ty
  | ptrToArray _ ty => ty
  end.

Canonical Structure type_system : TypeSystem.typeSystem := TypeSystem.TypeSystem type const index contentType.

Require Import Verse.Instruction.


Inductive Var v :=
| var : forall k (ty : type k), v k ty -> Var v.


Inductive statement v :=
| Inst       : forall ty : type TypeSystem.direct, instruction v ty -> statement v
| Next       : forall n (ty : type TypeSystem.direct), v TypeSystem.memory (ptrToArray n ty) -> statement v
| LoopDownTo : forall ty, v TypeSystem.direct ty -> list (statement v) -> statement v.

Record CFunction v := mkCFunction { parameters := list (Var v);
                                    locals     := list (Var v);
                                    body       := list (statement v);
                                  }.
