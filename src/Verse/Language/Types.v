Require Verse.TypeSystem.
Require Verse.Nibble.
Require Import Arith.
Import Nat.
Set Implicit Arguments.

(** printing power2m   $ 2^m     $ # 2<sup> m   </sup> # *)
(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)


(** * Types in its full glory.

The Verse EDSL is a typed machine language consisting of [word]s,
[multiword]s, and [array]s of which the first two, i.e. [word]s and
[multiword]s, can reside in the registers of the machine where as
[array]s are necessarily stored in the machine memory. The kind system
indicates this distinction in type.

*)
Inductive endian : Type := bigE | littleE | hostE.


Inductive type       : TypeSystem.kind -> Type :=
| word               : nat -> type TypeSystem.direct
| multiword          : nat -> nat    -> type TypeSystem.direct
| array              : nat -> endian -> type TypeSystem.direct -> type TypeSystem.memory
.

Definition const (t : type TypeSystem.direct) :=
  match t with
  | word n => Nibble.bytes (2^n)
  | multiword m n => Vector.t (Nibble.bytes (2^n))  (2 ^ m)
  end.

Canonical Structure verse_type_system : TypeSystem.typeSystem := TypeSystem.TypeSystem type const.


(** Compute the size of a type in bytes. *)
Fixpoint sizeOf {k} (ty : type k) :=
  match ty with
  | word n         => 2 ^ n
  | multiword m n  => 2 ^ m * 2 ^ n
  | array n _ tw => n * sizeOf tw
  end.


(** Often we need to existentially quantify over types and other
    objects. This definition is just for better readability.
 *)

Definition some {P: Type} (A : P -> Type) := sigT A.
