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

Inductive align :=
| aligned   : nat -> align  (* Aligned to 2^n bytes *)
.

Definition unaligned : align := aligned 0.

Inductive type       : kind -> Type :=
| word               : nat -> type direct
| multiword          : nat -> nat    -> type direct
| array              : align -> nat -> endian -> type direct -> type memory
with endian : Type := bigE | littleE | hostE.

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
  | array _ n _ tw  => Vector.t (typeDenote tw) n
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
(*
(** *** Bitwise and numeric functions.

Now that we know what the Verse type means as a type in Coq, we would
like to give meanings to some numeric and bitwise operators
operations.

*)

Require Import BinInt.



Fixpoint numBinaryDenote {k} (f : N -> N -> N) (t : type k)
  : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word _        => numBinOp f
  | multiword _ _ => Vector.map2 (numBinOp f)
  | array _ _ tw  => Vector.map2 (numBinaryDenote f tw)
  end.



Fixpoint numUnaryDenote {k}(f : N -> N)(t : type k)
  : typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 with
  | word      _   => numUnaryOp f
  | multiword _ _ => Vector.map (numUnaryOp f)
  | array  _ _ tw => Vector.map (numUnaryDenote f tw)
  end.

Fixpoint bitwiseBinaryDenote {k}(f : bool -> bool -> bool) (t : type k)
  : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word      _    => bitwiseBinOp f
  | multiword _ _  => Vector.map2 (bitwiseBinOp f)
  | array  _ _ tw  => Vector.map2 (bitwiseBinaryDenote f tw)
  end.

Fixpoint bitwiseUnaryDenote {k}(f : bool -> bool)(t : type k)
  : typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 with
  | word      _   => bitwiseUnaryOp f
  | multiword _ _ => Vector.map (bitwiseUnaryOp f)
  | array  _ _ tw => Vector.map (bitwiseUnaryDenote f tw)
  end.

 *)
