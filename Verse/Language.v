Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Syntax.
Require Vector.
Require Import List.
Require Import Coq.Sets.Ensembles.
Require Import Recdef.
Import String.
Require Import Basics.

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

  (** The verse assembly language is parameterised over the type [var]
      of typed variables *)

  Variable v   : type -> Type.

  (** ** Assembly language statements.

Verse support the implementation of simple C-callable [functions] in
assembly. A [function] in verse is set of [statements] which inturn
are instructions applied on appropriate arguments. Arguments,
represented in Coq using the type [arg], can be one of the following

- _Variables_ 

- _Constants_

- _indexed variables_


*)
  
  Inductive arg : type -> Type := 
  | var      {ty : type} : v ty -> arg ty
  | constant {ty : type} : constant ty -> arg ty
  | index {b : nat}{e : endian}{ty : type}
    : v (array b e ty) -> nat -> arg ty.

  Inductive assignment : Type :=
  | assign3 
    : forall ty, binop -> arg ty -> arg ty -> arg ty -> assignment
  (** e.g. x = y + z *)
  | assign2
    : forall ty, uniop -> arg ty -> arg ty -> assignment (** e.g. x = ~ y   *)
  | update2
    : forall ty, binop -> arg ty -> arg ty -> assignment (** e.g. x += y    *)
  | update1
    : forall ty, uniop -> arg ty -> assignment           (** e.g. x ~= x    *)
  .

  Inductive instruction : Type :=
  | assign : assignment -> instruction
  .

  Definition block := list instruction.

  (* Generic well-formed checks on instructions *)
  
  Inductive isLval {ty : type} : arg ty -> Prop :=
   | vIsLval {vr : v ty} : isLval (var vr)
   | indexIsLval {b : nat} {e : endian} {a : v (array b e ty)} {n}: isLval (index a n)
  .
  Definition wfTypes (ty : type) : Prop := True.

  Fixpoint wfvar (i : instruction) : Prop := 
    match i with
    | assign i => match i with
                  | assign3 ty _ v1 _ _ => and (isValue ty) (isLval v1)
                  | assign2 ty _ v1 _  => and (isValue ty) (isLval v1)
                  | update2 ty _ v1 _  => and (isValue ty) (isLval v1)
                  | update1 ty _ v1     => and (isValue ty) (isLval v1)
                  end
    end.
  
  Definition wfvarB (b : block) : Prop := fold_left and (map wfvar b) True.

End Language.

Arguments var [v ty] _ .
Arguments constant [v ty] _ .
Arguments index [v b e ty] _ _ .
Arguments assign3 [v ty] _ _ _ _ .
Arguments assign2 [v ty] _ _ _ .
Arguments update2 [v ty] _ _ _ .
Arguments update1 [v ty] _ _ .
Arguments assign [v] _ .

Arguments wfvarB [v] _ .

Lemma casesOpt {T : Type} (o : option T) : {t : T | o = Some t} + {o = None}.
Proof.
  exact 
  match o with
  | Some t => inleft (exist _ t eq_refl)
  | None   => inright (eq_refl)
  end.
Qed.

(* Helper functions for the Function module *)

Notation "A <= B <+> C " := (assign (assign3 plus  A B C))  (at level 20).
Notation "A <= B <-> C " := (assign (assign3 minus A B C))  (at level 20).
Notation "A <= B <*> C " := (assign (assign3 mul   A B C))  (at level 20).
Notation "A <= B </> C " := (assign (assign3 quot  A B C))  (at level 20).
Notation "A <= B <%> C " := (assign (assign3 rem   A B C))  (at level 20).
Notation "A <= B <|> C " := (assign (assign3 rem   A B C))  (at level 20).
Notation "A <= B <&> C " := (assign (assign3 rem   A B C))  (at level 20).
Notation "A <= B <^> C " := (assign (assign3 rem   A B C))  (at level 20).

Notation "A +<= B " := (assign (update2 plus  A B)) (at level 20).
Notation "A -<= B " := (assign (update2 minus A B)) (at level 20).
Notation "A *<= B " := (assign (update2 mul   A B)) (at level 20).
Notation "A /<= B " := (assign (update2 quot  A B)) (at level 20).
Notation "A %<= B " := (assign (update2 rem   A B)) (at level 20).
Notation "A |<= B " := (assign (update2 rem   A B)) (at level 20).
Notation "A &<= B " := (assign (update2 rem   A B)) (at level 20).
Notation "A ^<= B " := (assign (update2 rem   A B)) (at level 20).

Notation "A <=~ B "     := (assign (assign2 bitComp A B)) (at level 20).
Notation "A '<=RL' N B" := (assign (assign2 (rotL N) A B)) (at level 20).
Notation "A '<=RR' N B" := (assign (assign2 (rotR N) A B)) (at level 20).
Notation "A <=<< N B"   := (assign (assign2 (shiftL N) A B))
                             (at level 20).
Notation "A <=>> N B"   := (assign (assign2 (shiftR N) A B))
                             (at level 20).
(*Notation "'FOR' V 'IN' S 'DO' B" :=  (each V S B) (at level 20).*)

