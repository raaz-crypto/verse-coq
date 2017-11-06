Require Import Verse.Error.
Require Import Verse.Word.
Require Import Nat.



(** printing power2m   $ 2^m     $ # 2<sup> m   </sup> # *)
(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)

(** * Types in Verse.

The Verse EDSL is a typed machine language which has only two kinds of
types, multi-words and arrays. Multi-words capture words or vectors of
words and can be directly stored in registers where as arrays require
access to memory. The type [multiword m n] denotes a vector of
[power2m] words each of [power2n3] bits (the lowest word is 8-bit in
size). Arrays also carry around the endianness of the underlying
multiwords.

*)

Inductive kind  : Prop := direct | memory.

Inductive type       : kind -> Type :=
| word               : nat -> type direct
| multiword          : nat -> nat    -> type direct
| array              : nat -> endian -> type direct -> type memory
with endian : Type := bigE | littleE | hostE.


(** ** Sematics of [type].

The semantics of verse types is given by mapping it into types in
coq. A multiwordWhile the means of array and sequence are obvious, words are
usually of sizes [power2n] bytes for some [n]. Hence, [word n] denotes
words of [power2n] bytes and hence [typeDenote (word n)] is [Word.t
(power2n * power2p3) = Word.t power2np3]. Similary [vector n _]
denotes a vector of [power2n] elements.

*)

Fixpoint typeDenote {k : kind}(t : type k) : Type :=
  match t with
  | word      n    => Word.bytes (2^n)
  | multiword m n  => Vector.t (Word.bytes (2^n)) (2 ^ m)
  | array  n _ tw  => Vector.t (typeDenote tw) n
  end.

(** *** Bitwise and numeric functions.

Now that we know what the Verse type means as a type in Coq, we would
like to give meanings to some numeric and bitwise operators
operations.

*)

Require Import BinInt.



Fixpoint numBinaryDenote {k} (f : Z -> Z -> Z) (t : type k)
  : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word _        => numBinOp f
  | multiword _ _ => Vector.map2 (numBinOp f)
  | array _ _ tw  => Vector.map2 (numBinaryDenote f tw)
  end.



Fixpoint numUnaryDenote {k}(f : Z -> Z)(t : type k)
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
