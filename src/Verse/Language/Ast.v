
(** printing power2m   $ 2^m     $ # 2<sup> m   </sup> # *)
(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)


(** * The abstract syntax tree of Verse.

This module exposes the abstract syntax of the verse programming
language. The design takes the following points into consideration.

- A large number of instructions are shared across architectures. This
  include instructions that perform various arithmetic operations,
  bitwise operations etc.

- Certain architecture support various special registers like xmm
  registers, special instructions like native AES operations.


The design gives a portable way of expressing the former and
parameterise over the latter. Let us include arithmetic operators
first.

Some correctness and safety properties for features like array
indexing has been built into the ast and thus gives a correct by
construction style of AST.


We begin by defining the types for the language.

 *)


(* begin hide *)

Require Verse.TypeSystem.
Require Verse.Nibble.
Require Import Arith.
Require Import NArith.
Import Nat.
Set Implicit Arguments.

(* end hide *)

(** ** The type system for Verse.

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

Definition index (t : type TypeSystem.memory) :=
  match t with
  | array b _ _ => {i | i < b}
  end.

Definition contentType (t : type TypeSystem.memory) :=
  match t with
  | array _ _ ty => ty
  end.

Definition NToConst (ty : type TypeSystem.direct) (num : N) : const ty
  := match ty in type TypeSystem.direct return const ty with
     | word n => Nibble.fromN num
     | multiword m n => Vector.const (Nibble.fromN num) (2^m)
     end.

Definition natToConst (ty : type TypeSystem.direct) (num : nat) : const ty
  := match ty in type TypeSystem.direct return const ty with
         | word n => Nibble.fromNat num
         | multiword m n => Vector.const (Nibble.fromNat num) (2^m)
     end.

Canonical Structure verse_type_system : TypeSystem.typeSystem
  := TypeSystem.TypeSystem type const index contentType.




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

Definition logSize (ty : type TypeSystem.direct) : nat :=
  match ty with
  | word n => n
  | multiword m n => m + n
  end.
Definition size (ty : type TypeSystem.direct) : nat := 2 ^ logSize ty.

(* Array constructor *)
Definition Array  := array.
Definition Ref (ty : type TypeSystem.direct) : type TypeSystem.memory := array 1 hostE ty.

Require Import Verse.Instruction.

(* ** Verse Instructions

Other than common assignment, update, increment and decrement
instructions Verse support are two special instructions which deserve
some mention.

Firstly there is the [move] instruction that moves the value located
in an variable into the lhs. While move ensures that the value that is
currently in the variable on its rhs gets copied into the lhs, it
gives no guarantee on the value currently in its rhs. Assignments on
the other hand preserve the value of the rhs. This semantics of move
enable it to sometimes compile down to more efficient
instructions. For example, when moving a value from a variable [x] to
an array index [a[- i -]], which is of an endian different from that
of the machine, the move instruction needs to just endian switch [x],
and copy where as an assignment has to endian switch [x], copy and
then switch back.

The [clobber] instruction is like a no-op but it invalidates the
contents of a given variable. A move has the semantics of the
corresponding assignment followed by a clobber on the rhs.  Note that
the [clobber] and [move] need not erase the value in the rhs. So using
clobber to erase a secret value is not safe.  Typically clobber
instructions will be ignored when generating instructions.

 *)

Inductive specials v (ty : type TypeSystem.direct) : Type :=
| moveTo    : lexpr v ty -> v TypeSystem.direct ty  -> specials v ty
| clobber   : v TypeSystem.direct ty -> specials v ty.


Arguments clobber [v ty].

Inductive statement v :=
| generic : forall ty : type TypeSystem.direct, instruction v ty -> statement v
| special : forall ty : type TypeSystem.direct, specials v ty -> statement v.


Definition code v := list (statement v).


(**

Many cryptographic primitives work on streams of data that are divided
into chunks of fixed size. The record [iterator] is essentially the
body of the an iterator that works with such a stream of blocks of
type [ty].

*)
Record iterator (ty : type TypeSystem.memory) v
  := { setup    : code v;
       process  : v TypeSystem.memory ty -> code v;
       finalise : code v
     }.

(*

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

*)

(*
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Error.

Require Import Bool.
Require Import Omega.
Require Import List.
Import ListNotations.

Generalizable All Variables.
Set Implicit Arguments.

(* end hide *)

(** * The Verse language as an inductive data type.

*)

Require Export Verse.Language.Operators.

(** * The abstract syntax tree.

This section build up towards the the inductive type that capture the
verse language's abstract syntax tree. One of the most important
elements in a programming language is variables. In verse, program
fragments are parameterised by an abstract variable type that is used
through out.

*)

Section AST.

  Variable tyD : typeC TypeDenote.

  Variable v   : VariableT.


  (** Type that captures a memory variable's indices. *)
  Definition Indices {b e ty} (_ : v (array b e ty)) := { i : nat | i < b }.


  (** ** Arguments.

      Each verse program fragment consists of instructions applied to
      some arguments. Variables are one form of arguments, but so does
      indexed arrays or constants.

   *)

  Inductive argKind := lval | rval.
  Inductive arg : argKind -> VariableT :=
  | var   : forall aK, forall {k} {ty : type k}, v ty -> arg aK ty
  | const : forall {ty : type direct}, constant ty  -> arg rval ty
  | index : forall aK, forall {b : nat}{e : endian}{ty : type direct} (x : v (array b e ty)),
        Indices x  -> arg aK ty
  .

  Definition larg := arg lval.
  Definition rarg := arg rval.

  (** ** Assignment statement.

      One of the most important class of statement is the assignment
      statement. The following inductive type captures assignment statement.

   *)
  Inductive assignment : Type :=
  | assign3
    : forall (ty : type direct), binop -> larg ty -> rarg ty -> rarg ty -> assignment
  (** e.g. x = y + z *)
  | assign2
    : forall (ty : type direct), uniop -> larg ty -> rarg ty -> assignment (** e.g. x = ~ y   *)
  | update2
    : forall (ty : type direct), binop -> larg ty -> rarg ty -> assignment (** e.g. x += y    *)
  | update1
    : forall (ty : type direct), uniop -> larg ty -> assignment                   (** e.g. x ~= x    *)
  .

(**

Finally we have instructions that forms the basic unit of a program. A
program block is merely a list of instructions.

*)
  Inductive instruction : Type :=
  | assign    : assignment -> instruction
  | increment : forall (ty : type direct), larg ty -> instruction
  | decrement : forall (ty : type direct), larg ty -> instruction
  | moveTo    : forall b e ty, forall (x : v (array b e ty)), Indices x -> v ty -> instruction
  | clobber   : forall k (ty : type k), v ty -> instruction
  .

  Definition instructions := list instruction.

  Definition context := forall {k} {ty : type k}, v ty -> @typeDenote _ tyD _ ty.

  Definition ctxtP   := (context * context)%type.

  (*
     This particular design choice allows one to define a valid Prop even
     with a context that has some (unused) Invalid values.
     The simpler
                `pure_context -> Prop`
     would not allow one to extract a Prop with an impure context that has
     only unused Invalid values.
  *)

  Definition annotation := (ctxtP -> Prop).

  Inductive codeline : Type :=
  | assert : annotation  -> codeline
  | inst   : instruction -> codeline
  .

  Global Definition code := list codeline.
  (* begin hide *)

  (* Some instruction error checking code *)

  Definition isEndian {aK} {k} {ty : type k} (nHostE : endian) (a : arg aK ty) :=
    let eqEndb (e f : endian) : bool :=
        match e, f with
        | littleE, littleE
        | bigE, bigE       => true
        | _, _             => false
        end
    in
    match a  with
    | @index  _ _ ne _ _ _ => eqEndb ne nHostE
    | _                 => false
    end.

  (** Function to check if a non-mov/store instruction uses arrays of offending endianness.
      Passing hostE as parameter allows all arrays. **)

  Definition endianError (nHostE : endian) (i : instruction) :=
    match i with
    | assign e  =>
      match e with
      | assign2 nop _ _    => false
      | assign3 _ a1 a2 a3 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3)
      | assign2 _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
      | update2 _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
      | update1 _ a1       => (isEndian nHostE a1)
      end
    | _ => false
    end
  .

  Definition supportedInst (nhostE : endian) := fun i => endianError nhostE i = false.

  Definition instCheck e i : {supportedInst e i} + {~ supportedInst e i}
      := bool_dec (endianError e i) false.

  (* end hide *)


End AST.

Arguments Indices [v b e ty] _.
Arguments context [_] _.
Arguments annotation [tyD] _.
Arguments codeline [tyD] _.
Arguments inst [tyD v] _.
Arguments code [tyD] _.

Section ASTFinal.

  Variable t  : kind -> Type.
  Variable tC : typeC (fun k : kind => t k + {UnsupportedType}).

  Variable constT : t direct -> Type.

  (* We abandon index safety at the machine level *)

  Class argC (a : GenVariableT t -> GenVariableT t) :=
    { mkVar : forall v k (ty : t k), v k ty -> a v k ty;
      mkConst : forall v (ty : t direct), constT ty -> a v direct ty;
      mkIndex : forall v (b : nat) (e : endian) (ty : t direct)
                (p : noErr (mkArray b e {- ty -})), v memory (getT p)
                -> nat -> a v direct ty
    }.

  (** An alternate way would be to write -

        Variable v : GenVariableT t.

        Class argC (a : GenVariableT t) := ...

      This would then allow, for example, an architecture to allow
      arrays to be pointed to by only some of it's registers.
  *)

  Variable vT : GenVariableT t.
  Variable aT  : GenVariableT t -> GenVariableT t.

  (* Since the instruction type for an architecture will be defined
     specifically for it's machineVar, instT is just a plain type
  *)

  Class instructionC (instT : Type) :=
    { UnsupportedInstruction : Prop;
      mkIncrement : forall ty : t direct, aT vT ty ->
                                          instT + {UnsupportedInstruction};
      mkDecrement : forall ty : t direct, aT vT ty ->
                                          instT + {UnsupportedInstruction};
      mkUpdate1 : forall ty : t direct, uniop ->
                                        aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkUpdate2 : forall ty : t direct, binop ->
                                        aT vT ty -> aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkAssign2 : forall ty : t direct, uniop ->
                                        aT vT ty -> aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkAssign3 : forall ty : t direct, binop ->
                                        aT vT ty -> aT vT ty -> aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkMoveTo : forall b e ty (p : noErr (mkArray b e {- ty -})), vT (getT p) -> nat -> vT ty ->
                                                                   instT + {UnsupportedInstruction};
      mkNOP : instT (* A NOP instruction for CLOBBER translate.
                       This could, in a string translate, simply be
                       the empty string
                     *)
    }.

End ASTFinal.

Arguments instructionC [t _] _ _ _.
(* The following implicit argument declarations seem to be necessary to
   use the constructs without arguments. This is inspite of all arguments
   being implicit, albeit not maximally inserted, even prior to these
   declarations
*)
Arguments UnsupportedInstruction [t tC vT aT instT instructionC].
Arguments mkIncrement {t tC vT aT instT instructionC ty} _.
Arguments mkDecrement {t tC vT aT instT instructionC ty} _.
Arguments mkNOP [t tC vT aT instT instructionC].

(* begin hide *)
Arguments iterator [tyD] _ _.
Arguments setup [tyD ty v] _.
Arguments process [tyD ty v] _ _.
Arguments finalise [tyD ty v] _.

Arguments var [v aK k ty] _ .
Arguments const [v ty] _ .
Arguments index [v aK  b e ty]  _ _.
Arguments assign3 [v ty] _ _ _ _ .
Arguments assign2 [v ty] _ _ _ .
Arguments update2 [v ty] _ _ _ .
Arguments update1 [v ty] _ _ .
Arguments assign [v] _ .
Arguments increment [v ty] _.
Arguments decrement [v ty] _.
Arguments moveTo [v  b e ty] _ _ _.
Arguments clobber [v k ty ] _.
(* end hide *)
*)