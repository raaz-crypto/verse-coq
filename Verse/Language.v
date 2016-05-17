(** * The abstract syntax

This module exposes the abstract syntax of the verse programming
language.

 *)

Require Import Verse.Types.
Require Import String.

Inductive arity := binary | unary.
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

  Variable r   : forall k : kind,  type k -> Type. Arguments r [k] _.
  Variable i   : Type.

  Inductive var : forall {k : kind}, type k -> Type :=
  | register {k : kind}{ty : type k} : r ty -> var ty
  | stack    {k : kind}(ty : type k) : nat  -> var ty.

  Inductive arg : forall {k : kind}, type k -> Type :=
  | param    {k : kind}(ty : type k) : nat  -> arg ty
  | v        {k : kind}{ty : type k} : var ty -> arg ty
  | const    {k : kind}{ty : type k} : constant ty -> arg ty
  | index {b : nat}{e : endian}{v : value}{ty : valuetype v}
    : arg (array b e ty) -> arg ty.


  (*| immediate {v : value}{ty : valuetype v} : constant ty -> arg ty.*)

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


  Definition parameter {k : kind}(ty : type k) : someType
    := existT type k ty.


  Fixpoint body {n : nat}(ps : Vector.t someType n)(A : Type) : Type :=
    match ps with
      | []                  => A
      | (existT _ ty) :: xs => arg ty -> body xs A
    end.


  Fixpoint function {A : Type}{n : nat}(ps : Vector.t someType n)
  : body ps A  -> A :=
    match ps with
      | []
        => (fun f : body [] A -> A => f) (fun X : A => X)
      | existT _ ty :: qs
        => fun f : body (existT _ _ ty :: qs) A
           => function qs (f (param ty n))

    end.

End Language.

Arguments body [r n]  _ _.
Arguments function [r A n] _ _.

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
