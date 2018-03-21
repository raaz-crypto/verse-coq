Require Import Verse.Error.
Require Import Verse.Word.
Require Import Arith.
Import Nat.

(** printing power2m   $ 2^m     $ # 2<sup> m   </sup> # *)
(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)

(** * Types in full detail.

The Verse EDSL is a typed machine language consisting of [word]s,
[multiword]s, and [array]s of which the first two, i.e. [word]s and
[multiword]s, can reside in the registers of the machine where as
[array]s are necessarily stored in the machine memory. The kind system
indicates this distinction in type.

*)

Inductive kind  : Type := direct | memory.

Inductive type       : kind -> Type :=
| word               : nat -> type direct
| multiword          : nat -> nat    -> type direct
| array              : nat -> endian -> type direct -> type memory
with endian : Type := bigE | littleE | hostE.

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

(** ** Sematics of [type]'s.

We need to provide a meaning to [type]'s by representing them in coq.
As the base case, we need to specify what words mean. Multi-words
[multiword m n] are then defined as a vectors of over the word type
word type, and finally arrays are vectors over the element type. To
support maximum flexibility, meaning of type are parameterised by the
definition of the word.

*)

Require Import PrettyPrint.
Module Type WORD_SEMANTICS.
  Parameter wordDenote : nat -> Type.
End WORD_SEMANTICS.

Module TypeDenote (W : WORD_SEMANTICS).

  Fixpoint typeDenote {k : kind}(t : type k) : Type :=
  match t with
  | word      n    => W.wordDenote n
  | multiword m n  => Vector.t (W.wordDenote n) (2 ^ m)
  | array n _ tw   => Vector.t (typeDenote tw) n
  end.

  Arguments typeDenote [k] _.
End TypeDenote.


(** *** The Standard word.

We now define the standard word semantics. In this semantics the type [word n]
denotes unsigned words of [power2n] bits.

*)



Module StandardWord.
  Definition wordDenote n := Word.bytes (2^n).
End StandardWord.


Global Instance word_constant_pretty n : PrettyPrint (StandardWord.wordDenote n) := word_pretty (8 * 2^n).

Module StandardType := TypeDenote(StandardWord).

Export StandardType.
