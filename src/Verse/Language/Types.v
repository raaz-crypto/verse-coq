(* begin hide *)
Require Verse.Nibble.
Require Import Verse.TypeSystem.
Require Import Arith.
Require Import NArith.
Require Import Bvector.
Require Import BinNat.
(* end hide *)

(** ** The type system for Verse.

The Verse EDSL is a typed machine language consisting of [word]s,
[multiword]s, and [array]s of which the first two, i.e. [word]s and
[multiword]s, can reside in the registers of the machine where as
[array]s are necessarily stored in the machine memory. The kind system
indicates this distinction in type.

*)

Inductive type       : kind -> Type :=
| word               : nat -> type direct
(* TODO : Maybe make `word` a `multiword 0`. Might save stuff *)
| multiword          : nat -> nat    -> type direct
| array              : nat -> endian -> type direct -> type memory.

(** Size of a word in bits *)
Definition bitSize sz := 4 * (2 * 2^sz).

(** This is what a word of size means as a bit vector *)
Definition BWord sz := Bvector (bitSize sz).

Definition const (t : type direct) :=
  match t with
  | word sz => BWord sz
  | multiword m sz => Vector.t (BWord sz)  (2 ^ m)
  end.

Definition NToConst (ty : type direct) (num : N) : const ty
  := let numtrunc sz : BWord sz := N2Bv_sized _ num in
     match ty in type direct return const ty with
     | word sz => numtrunc sz
     | multiword m sz => Vector.const (numtrunc sz) (2^m)
     end.

Definition natToConst (ty : type direct) (num : nat) : const ty
  :=  NToConst ty (N.of_nat num).

(** * Operators of Verse language.

We define the arithmetic and bitwise operators that the verse language
supports. Target languages have support for these. The nat parameter
captures the arity of the operator. The shifts and rotate instructions
are arity one here because they only support constant
offsets. Cryptographic implementations only need this and infact it is
better to restrict to such shifts/rotates --- argument dependent
shifts and rotates can become side channel leaking instructions.

 *)

Inductive op : nat -> Set :=
| plus    : op 2
| minus   : op 2
| mul     : op 2
| quot    : op 2
| rem     : op 2
| bitOr   : op 2
| bitAnd  : op 2
| bitXor  : op 2
| bitComp : op 1
| shiftL  : nat -> op 1
| shiftR  : nat -> op 1
| rotL    : nat -> op 1
| rotR    : nat -> op 1
.

(** Standard word types/scalars *)
Notation Byte   := (word 0).
Notation Word8  := (word 0).
Notation Word16 := (word 1).
Notation Word32 := (word 2).
Notation Word64 := (word 3).

(**
The logSize of a direct type measures the size of the word in
logarithmic scale.  This is often a convenient way to measure the
length because of the fact that [word n] type denotes the word of
[2^n] bytes.
*)

Definition logSize (ty : type direct) : nat :=
  match ty with
  | word n => n
  | multiword m n => m + n
  end.
Definition size (ty : type direct) : nat := 2 ^ logSize ty.

(* Array constructor *)
Definition Array  := array.
Definition Ref (ty : type direct) : type memory := array 1 hostE ty.

Canonical Structure verse_type_system := TypeSystem type array const (fun t => op).

Definition VariableT := Variables.U verse_type_system.

(** ** Translating verse types.

To define translations from verse types, all we need is translations
of direct types which we can use to [extend] it to the entire universe
of verse types.

 *)

Section VerseTranslation.

  Variable ts  : typeSystem.
  Variable tf  : type direct -> typeOf ts direct.
  Variable cf  : forall ty, const ty -> constOf ts (tf ty).
  Variable opf : forall ty n, op n ->  operator ts (tf ty) n.

  Definition extend : forall k, type k -> typeOf ts k :=
    fun k => match k as k0 return type k0 -> typeOf ts k0 with
          | direct => tf
          | memory => fun ty : type memory =>
                       match ty with
                       | array b e stype => arrayType ts b e (tf stype)
                       end
          end.

  Lemma extends_to_array : forall b e ty,
      extend memory (array b e ty) = arrayType ts b e (extend direct ty).
  Proof.
    intros; trivial.
  Defined.

  Definition verseTranslation := TypeTranslation extend cf opf extends_to_array.

End VerseTranslation.

Arguments verseTranslation [ts].
