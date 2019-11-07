(* begin hide *)
Require Verse.Nibble.
Require Import Verse.TypeSystem.
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

Inductive type       : kind -> Type :=
| word               : nat -> type direct
| multiword          : nat -> nat    -> type direct
| array              : nat -> endian -> type direct -> type memory.

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

Canonical Structure verse_type_system := TypeSystem type array const.

(** * Type translation and compilation.

A type translation is mapping between the types of two type systems
which preserves the constants. A compilation is a translation which
can err --- it might be the case that certain types in the source type
system might not have faithful representation in the type system. We
represent type translation using the following structure.

 *)

Structure translator (ts0 ts1 : typeSystem)
  := TypeTranslation { typeTrans   : forall k, typeOf ts0 k -> typeOf ts1 k;
                       constTrans  : forall ty : typeOf ts0 direct,
                           constOf ts0 ty -> constOf ts1 (typeTrans direct ty);
                       arrayCompatibility : forall b e ty,
                           typeTrans memory (arrayType ts0 b e ty) = arrayType ts1 b e (typeTrans direct ty)
                     }.

Arguments TypeTranslation [ts0 ts1].
Arguments typeTrans [ts0 ts1] _ [k].
Arguments constTrans [ts0 ts1] _ [ty].
Arguments arrayCompatibility [ts0 ts1].

(** ** Type compilation and result types.

For an arbitrary target type system [ts], type compilation into [ts]
can also be represented by the [typeTranslation] structure by first
considering the types [resultType ts] and the associated type system
[resultSystem ts]. Type compilation to [ts] can then be seen as a type
transaltion into [resultSystem ts].

*)

Require Import Verse.Error.

(* ** Translation results *)

Definition resultSystem ts :=
  let resultType ts k := typeOf ts k + {TranslationError} in
  let resultArray ts b e : resultType ts direct -> resultType ts memory
      := ap (arrayType ts b e) in
  let resultConst ts  (ty : resultType ts direct) :=
      match ty with
      | {- tyC -} => constOf ts tyC
      | _         => Empty_set + {TranslationError}
      end in

  TypeSystem (resultType ts) (resultArray ts) (resultConst ts).

Definition compiler src ts := translator src (resultSystem ts).

(** ** Translating verse types.

To define translations from verse types, all we need is translations
of direct types which we can use to [extend] it to the entire universe
of verse types.

 *)

Section VerseTranslation.

  Variable ts : typeSystem.
  Variable tf : type direct -> typeOf ts direct.
  Variable cf : forall ty, const ty -> constOf ts (tf ty).

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

  Definition verseTranslation := TypeTranslation extend cf extends_to_array.

End VerseTranslation.

Arguments extend [ts].
Arguments extends_to_array [ts].
Arguments verseTranslation [ts].

(** ** Typed variables.

When building programming constructs, we need variables. In a typed
setting, we would like the variables to be parameterised by types. The
[VariableT ts] should be seen as the universe of program variables for
programs that use the type system [ts].

*)

Definition VariablesOf (ts : typeSystem) := forall k, typeOf ts k -> Set.
Definition VariableT := VariablesOf verse_type_system.

Import Vector.VectorNotations.
(** A declaration is just a sequence of types *)
Definition Declaration n
  := Vector.t (some type) n.

Arguments Declaration [n].

Definition Empty : Declaration    := [].

(** Helper function that recovers the type of the given variable *)
Definition Var {v : VariableT}{k}{t : type k}
  : v k t -> some type
  := fun _ => existT _ _ t.
