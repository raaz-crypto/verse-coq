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

(* ** Semantics for the Verse language.

In the case of the verse language (i.e where our type system is the
[verse_type_system]), we need to only specify the translation for the
[word n] type. We use the [fromWordDenote] function to convert it to
an element of [typeDenote verse_type_system] giving semantics for the
verse language. We define this function inside a section to manage the
verbosity of the types.

*)

Section WordTypeDenote.

  (** We need to give three things to get a [typeDenote
     verse_type_system]

     - A function [wordOfSize] which gives the type associated to the
        verse type [word n],

     - A [const] function which for every [n] gives a way to convert
        the verse constant of type [word n] to [wordOfSize n],

     - A [oper] function that interprets verse operators for [wordOfSize n].

  *)

  Variable wordOfSize : nat -> Type.
  Variable const      : forall sz, constOf verse_type_system (word sz) -> wordOfSize sz.
  Variable oper       : forall sz arity, op arity -> nary (wordOfSize sz) arity.

  Fixpoint typeConv k (ty : type k)  : typeOf abstract_type_system k :=
    match ty with
    | word sz => wordOfSize sz
    | multiword m sz => Vector.t (wordOfSize sz) (2^m)
    | array b e ty  => Vector.t (typeConv direct ty) b
    end.

  Definition constConv (ty : type direct)
    :  constOf verse_type_system ty  -> typeConv direct ty
    := match
        ty as ty0 in (type k)
        return
        (match k as x return (type x -> Type) with
         | direct => fun t : type direct => constOf verse_type_system t -> typeConv direct t
         | memory => fun _ : type memory => IDProp
         end ty0)
      with
      | word n => const n
      | multiword m n => Vector.map (const n)
      | array _ _ _ => idProp
      end.

  Definition vectorApp {A B}{n}(fvec : Vector.t (A -> B) n) (vec : Vector.t A n) : Vector.t B n
    := Vector.map2 (fun f x => f x) fvec vec.
  Fixpoint appN {T} {m} arity : Vector.t (nary T arity) m ->  nary (Vector.t T m) arity
    := match arity with
       | 0 => fun x => x
       | S r => fun fvec vec => appN r (vectorApp fvec vec)
       end.

  Fixpoint opConvGen {k} (ty : type k) arity (o : op arity)
    : nary (typeConv k ty) arity
    := match ty as ty0 in type k0
             return  nary (typeConv k0 ty0) arity
       with
       | word sz =>  oper sz arity o
       | multiword m sz  =>
         appN  arity (Vector.const (oper sz arity o) (2^m))
       | array b e ty0 => appN arity (Vector.const (opConvGen ty0 arity o) b)
       end.
  Definition opConv := @opConvGen direct.

  Definition fromWordDenote :  typeDenote verse_type_system :=
    {| typeTrans  := typeConv;
       constTrans := constConv;
       opTrans    := opConv;
       arrayCompatibility := fun _ _ _ => eq_refl
    |}.
End WordTypeDenote.
