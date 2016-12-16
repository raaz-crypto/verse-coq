Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Vector.
Import List.ListNotations.
Import String.

(** * The abstract syntax

This module exposes the abstract syntax of the verse programming
language. The design takes the following points into consideration.

- A large number of instructions are shared across architectures. This
  include instructions that perform various arithmetic operations,
  bitwise operations etc.

- Certain architecture support various special registers like xmm
  registers, special instructions like native AES operations.

The design gives a portable way of expressing the former and parameterise
over the latter.

** Arithmetic and bitwise operators.

Most architectures allow various basic arithmetic, bitwise operations
on values stored in the registers. These instructions can be of
arity unary or binary.

*)
Inductive arity := binary | unary.

(**

Having defined the arity, we have the generic operations supported by
most architectures.

*)

Inductive op    : arity -> Type :=
| plus    : op binary
| minus   : op binary
| mul     : op binary
| quot    : op binary
| rem     : op binary
| bitOr   : op binary
| bitAnd  : op binary
| bitXor  : op binary
| bitComp : op unary
| rotL    : nat -> op unary
| rotR    : nat -> op unary
| shiftL  : nat -> op unary
| shiftR  : nat -> op unary
.

Definition binop := op binary.
Definition uniop := op unary.

Section Language.

  (** ** Architecture specific portions.

Architectures differs in what registers they have and what special
instructions they support. To capture this variability in the
architecture the verse assembly language is parameterised over these
two quantities.

   *)

  Variable r     : type -> Type.
  Variable var   : type -> Type.
  Variable i     : (type -> Type) -> Type.

  (** ** Assembly language statements.

Verse support the implementation of simple C-callable [functions] in
assembly. A [function] in verse is set of [statements] which inturn
are instructions applied on appropriate arguments. Arguments,
represented in Coq using the type [arg], can be one of the following

- _Variables_ represented in Coq using the type [var].

- _Constants_

- _indexed variables_


*)
  
  Inductive arg : type -> Type :=
  | v        {ty : type} : var ty -> arg ty
  | const    {ty : type} : constant ty -> arg ty
  | index {b : nat}{e : endian}{ty : type}
    : arg (array b e ty) -> arg ty.


  Inductive assignment : Type :=
  | assign3  {ty : type}
    : binop -> arg ty -> arg ty -> arg ty -> assignment
  (** e.g. x = y + z *)
  | assign2 {ty : type}
    : uniop -> arg ty -> arg ty -> assignment  (** e.g. x = ~ y   *)
  | update2 {ty : type}
    : binop -> arg ty -> arg ty -> assignment (** e.g. x += y    *)
  | update1 {ty : type}
    : uniop -> arg ty -> assignment           (** e.g. x ~= x    *)
  .

  Inductive statement : Type :=
  | assign   : assignment -> statement
  | specials : i arg      -> statement
  | each {ty : type} :
      var ty  -> arg (sequence ty) -> list statement -> statement
  .

  Definition statements := list statement.

  Definition varSpec    := sigT var.
  Definition context    := list varSpec.

  Record function : Type
    := makeFunction { name    : string;
                      params  : context;
                      locals  : context; 
                      body    : statements;
                    }.

End Language.

(**


 *)


Notation "A <= B <+> C " := (assign (assign3 _ plus  A B C))  (at level 20).
Notation "A <= B <-> C " := (assign (assign3 _ minus A B C))  (at level 20).
Notation "A <= B <*> C " := (assign (assign3 _ mul   A B C))  (at level 20).
Notation "A <= B </> C " := (assign (assign3 _ quot  A B C))  (at level 20).
Notation "A <= B <%> C " := (assign (assign3 _ rem   A B C))  (at level 20).
Notation "A <= B <|> C " := (assign (assign3 _ rem   A B C))  (at level 20).
Notation "A <= B <&> C " := (assign (assign3 _ rem   A B C))  (at level 20).
Notation "A <= B <^> C " := (assign (assign3 _ rem   A B C))  (at level 20).

Notation "A +<= B " := (assign (update2 _ plus  A B)) (at level 20).
Notation "A -<= B " := (assign (update2 _ minus A B)) (at level 20).
Notation "A *<= B " := (assign (update2 _ mul   A B)) (at level 20).
Notation "A /<= B " := (assign (update2 _ quot  A B)) (at level 20).
Notation "A %<= B " := (assign (update2 _ rem   A B)) (at level 20).
Notation "A |<= B " := (assign (update2 _ rem   A B)) (at level 20).
Notation "A &<= B " := (assign (update2 _ rem   A B)) (at level 20).
Notation "A ^<= B " := (assign (update2 _ rem   A B)) (at level 20).

Notation "A <=~ B "     := (assign (assign2 _ bitComp A B)) (at level 20).
Notation "A '<=RL' N B" := (assign (assign2 _ (rotL N) A B)) (at level 20).
Notation "A '<=RR' N B" := (assign (assign2 _ (rotR N) A B)) (at level 20).
Notation "A <=<< N B"   := (assign (assign2 _ (shiftL N) A B))
                             (at level 20).
Notation "A <=>> N B"   := (assign (assign2 _ (shiftR N) A B))
                             (at level 20).
Notation "'FOR' V 'IN' S 'DO' B" :=  (each V S B) (at level 20).
