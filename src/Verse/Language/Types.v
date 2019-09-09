(* begin hide *)
Require Verse.Nibble.
Require Import Arith.
Require Import NArith.
(* end hide *)

(** ** The type system for Verse.

The Verse EDSL is a typed machine language consisting of [word]s,
[multiword]s, and [array]s of which the first two, i.e. [word]s and
[multiword]s, can reside in the registers of the machine where as
[array]s are necessarily stored in the machine memory. The kind system
indicates this distinction in type.

*)

Inductive kind := direct | memory.
Inductive type       : kind -> Type :=
| word               : nat -> type direct
| multiword          : nat -> nat    -> type direct
| array              : nat -> endian -> type direct -> type memory
with endian : Set := bigE | littleE | hostE.

Definition const (t : type direct) :=
  match t with
  | word n => Nibble.bytes (2^n)
  | multiword m n => Vector.t (Nibble.bytes (2^n))  (2 ^ m)
  end.

Definition NToConst (ty : type direct) (num : N) : const ty
  := match ty in type direct return const ty with
     | word n => Nibble.fromN num
     | multiword m n => Vector.const (Nibble.fromN num) (2^m)
     end.

Definition natToConst (ty : type direct) (num : nat) : const ty
  := match ty in type direct return const ty with
         | word n => Nibble.fromNat num
         | multiword m n => Vector.const (Nibble.fromNat num) (2^m)
     end.

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


(** * Type Systems.

Verse has a strong type system that catch a lot of bugs at compile
time.  The targets that verse compile to is also expected to share a
few features of the verse type system. For example, it has a notion of
direct types and memory types. It has a way to build array of direct
types. Target languages might choose to ignore some aspects, like for
example arrays do not carry a notion of endianness in C, but the
translation process from verse to the target language is expected to
take care of these. One can view this as a erasure of some of the
typing information as we compile to a low level target language.

*)

Structure typeSystem :=
  TypeSystem { typeOf       : kind -> Set;
               arrayType    : nat -> endian -> typeOf direct -> typeOf memory;
               constOf      : typeOf direct -> Type;
             }.


Canonical Structure verse_type_system := TypeSystem type array const.

(** ** Typed variables.

When building programming constructs, we need variables. In a typed
setting, we would like the variables to be parameterised by types. The
[VariableT ts] should be seen as the universe of program variables for
programs that use the type system [ts].

*)

Definition VariablesOf (ts : typeSystem) := forall k, typeOf ts k -> Set.
Definition VariableT := VariablesOf verse_type_system.

(** * Type translation

 *)

Require Import Verse.Error.

(* ** Translation results *)

Definition resultType ts k    := typeOf ts k + {TranslationError}.
Definition resultArray ts b e : resultType ts direct -> resultType ts memory
  := ap (arrayType ts b e).
Definition resultConst ts  (ty : resultType ts direct) :=
  match ty with
  | {- tyC -} => constOf ts tyC
  | _         => Empty_set + {TranslationError}
  end.


Definition typeMap ts
  := type direct -> resultType ts direct.

Definition resultSystem ts :=
  TypeSystem (resultType ts) (resultArray ts) (resultConst ts).


Structure typeTranslation (ts : typeSystem)
  := TypeTranslation { typeTrans   : type direct -> typeOf ts direct;
                       constTrans  : forall ty : type direct,
                           const ty -> constOf ts (typeTrans ty)
                     }.

Arguments TypeTranslation [ts].
Definition typeCompile ts := typeTranslation (resultSystem ts).