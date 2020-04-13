Require Import Verse.TypeSystem.
Require Import Verse.Nibble.
Require Verse.Error.

(** * The type of C

We now capture the type system for C. Only types that arise in
translation of verse code is captured here.

 *)

Inductive type  : kind -> Set :=
| uint8_t       : type direct
| uint16_t      : type direct
| uint32_t      : type direct
| uint64_t      : type direct
| array         : nat -> type direct -> type memory
| ptrToArray    : nat -> type direct -> type memory
.

Definition carrayType n (e : endian) t := array n t.

Definition const (ty : type direct) := list Nibble.


(** * The expression language.

We begin by defining C expressions. Since C is our target language,
and not a source language, its role is merely in obtaining the pretty
printed code. Therefore, being not too strict in the types would aid
us considerably.

 *)

Require Verse.Language.Types.

(** The operators of C are the operators of the verse source language *)
Definition op := Types.op.

Definition c_type_system :=
    TypeSystem  type carrayType const (fun t => op).

(** * Explanation for the constructors.

Essentially, C expressions are Verse operators applied to
subexpressions. However, there are some additional constructors which
we now explain.

- The constructors [rotateL] and [rotateR] for calls to C functions
  that implement the rotate instructions. For some strange reason C
  does not have rotate instructions.

- [convert_to] and [convert_from] for endian conversion functions.

- [verse_u8, verse_u16, verse_u32, verse_u64] for constant creation.
  The limitation of the notation system to combine nibbles without
  interleaving spaces meant we need a hack to get this working.

*)


Require Vector.
Require Import Verse.Nibble.
Import Vector.VectorNotations.

Module Expr.

  Inductive voidparams : Set.

  Inductive expr :=
  | app            : forall n, op n -> Vector.t expr n -> expr
  | index          : expr -> nat -> expr
  | ptrDeref       : expr -> expr
  | rotateL        : type direct -> expr * nat -> expr
  | rotateR        : type direct -> expr * nat -> expr
  | convert_to     : endian -> type direct -> expr -> expr
  | convert_from   : endian -> type direct -> expr -> expr
  | verse_const    : forall ty, const ty -> expr
  | gt_zero        : expr -> expr.
  Arguments app [n].
End Expr.


Import Expr.

(** ** Variables and Constants as expressions.

Constants and variables are also represented by expressions. This is
an over-approximation of the situation as constants and variables are
only subclasses of expressions. However, since our interest is only in
the pretty printed form, this is not really a problem.

 *)


Definition cvar k (ty : type k) := Expr.expr.

Inductive declaration :=
| declare_variable : forall k (ty : type k), cvar k ty -> declaration.

Definition declare k ty := declare_variable k ty.

Inductive parameters := params : list declaration -> parameters.

Inductive statement :=
| declareStmt : declaration  -> statement
| assign      : expr -> expr -> statement
| update      : expr -> forall n, op (S n) -> Vector.t expr n -> statement
| increment   : expr -> statement
| decrement   : expr -> statement
| comment   : forall Text , Text -> statement
| whileLoop : expr -> braces -> statement
with braces := Braces : list statement -> braces.

Inductive line :=
| include   : forall FileName,  FileName -> line
| defineXOR : line
| function  : forall FN,  FN -> parameters -> braces -> line.

Inductive program :=
| Program : list line -> program.

(* begin hide *)
Arguments update _ [n].

Arguments cvar [k].
Arguments declare_variable [k].
Arguments declare [k ty].
Arguments function [FN].
Arguments include [FileName].

Inductive headers := stdint_h | verse_h.

Notation "'stdint.h'" := (stdint_h) (only printing).
Notation "'verse.h'"  := (verse_h)  (only printing).

Import List.ListNotations.

(* end hide *)
(** Generates a complete verse C file with necessary includes *)
Definition verseC l := Program ([ include stdint_h ; include verse_h ; defineXOR ] ++ l)%list.
