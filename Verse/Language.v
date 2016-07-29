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

  Variable r   : forall {k : kind},  type k -> Type.
  Variable i   : Type.

  (* begin hide *)
  (* hide implicit argument declaration for registers *)
  Arguments r [k] _.
  (* end hide *)

  (** ** Assembly language statements.

Verse support the implementation of simple C-callable [functions] in
assembly. A [function] in verse is set of [statements] which inturn
are instructions applied on appropriate arguments. Arguments,
represented in Coq using the type [arg], can be one of the following

- _Variables_ represented in Coq using the type [var].

- _Constants_

- _indexed variables_


*)
  Inductive var : forall {k : kind}, type k -> Type :=
  | register {k : kind}{ty : type k} : r ty -> var ty
  | stack    {k : kind}(ty : type k) : nat  -> var ty
  | param    {k : kind}(ty : type k) : nat  -> var ty
  .

  Inductive arg : forall {k : kind}, type k -> Type :=
  | v        {k : kind}{ty : type k} : var ty -> arg ty
  | const    {k : kind}{ty : type k} : constant ty -> arg ty
  | index {b : nat}{e : endian}{v : value}{ty : valuetype v}
    : arg (array b e ty) -> arg ty.


  Inductive assignment : Type :=
  | assign3  {v : value}{ty : type (valueK v)}
    : binop -> arg ty -> arg ty -> arg ty -> assignment
  (** e.g. x = y + z *)
  | assign2 {v : value}{ty : type (valueK v)}
    : uniop -> arg ty -> arg ty -> assignment  (** e.g. x = ~ y   *)
  | update2 {v : value}{ty : type (valueK v)}
    : binop -> arg ty -> arg ty -> assignment (** e.g. x += y    *)
  | update1  {v : value}{ty : type (valueK v)}
    : uniop -> arg ty -> assignment           (** e.g. x ~= x    *)
  .

  Inductive statement : Type :=
  | assign   : assignment -> statement
  | specials : i          -> statement
  | each  {b : bound}{ty : type (Bounded b)} :
      var ty  -> arg (sequence ty) -> list statement -> statement
  .

  Definition statements := list statement.

  Definition typeSpec   := sigT type.
  Definition context    := list typeSpec.

  Definition variable {k : kind}(ty : type k) := existT type k ty.

  Record block   : Type
    := makeBlock { locals       : context;
                   instructions : statements
                 }.

  Record function : Type
    := makeFunction { name    : string;
                      params  : context;
                      body    : block
                    }.


  (* begin hide *)
  Local Open Scope list_scope.

  Fixpoint allocType (cs : context)(B : Type)
    := match cs with
         | []                 => B
         | existT  _ _ ty :: vsP => arg ty -> allocType vsP B
       end.

  Fixpoint allocVar
           (mkV : forall (k : kind) (ty : type k), nat -> var ty)
           (n : nat)(cs : context)(B : Type)
  : allocType cs B -> B
    := match cs with
         | []
           => fun b : allocType [] B => b
         | existT _ k ty :: csP
           => fun f : arg ty -> allocType csP B
              =>  allocVar mkV (S n) csP B (f (v (mkV k ty n)))
       end.

  (* end hide *)

   (** * Allocating variables.

Constructing the function definition directly is inconvinient and
error prone particularly when parameter indices are in question. The
combinators [defun] and [local] can be used for this purpose.
  *)


  Definition defun (nm : string)(ps : context)
  : forall f : allocType ps block, function
    := fun f => makeFunction nm ps (allocVar (@param) 1 ps block f).

  Definition local (ps : context)
  : forall f : allocType ps statements, block
    := fun f => makeBlock ps (allocVar (@stack) 1 ps statements f).

End Language.


Arguments defun [r i] _ _ _.
Arguments local [r i] _ _.

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
