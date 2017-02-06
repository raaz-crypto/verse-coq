Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Vector.
Require Import Coq.Sets.Ensembles.
Require Import List.
Require Import Recdef.
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

  Variable var   : type -> Type.

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
  | constant {ty : type} : constant ty -> arg ty
  | index {b : nat}{e : endian}{ty : type}
    : arg (array b e ty) -> arg ty.

  Inductive assignment {ty : type} : Type :=
  | assign3 
    : binop -> arg ty -> arg ty -> arg ty -> assignment
  (** e.g. x = y + z *)
  | assign2
    : uniop -> arg ty -> arg ty -> assignment (** e.g. x = ~ y   *)
  | update2
    : binop -> arg ty -> arg ty -> assignment (** e.g. x += y    *)
  | update1
    : uniop -> arg ty -> assignment           (** e.g. x ~= x    *)
  .

  Inductive instruction : Type :=
  | assign : forall ty : type,  @assignment ty -> instruction
  .

  Definition block := list instruction.

  (*Definition isLval {ty : type} (a : arg ty) : Prop := True.*)
  Inductive isLval {ty : type} : arg ty -> Prop :=
   | vIsLval {vr : var ty} : isLval (v vr)
   | indexIsLval {b : nat} {e : endian} {a : arg (array b e ty)}: isLval (index a)
  .
  Definition wftypes (i : instruction) : Prop := True.

  Fixpoint wftypesb (b : block) : Prop :=
    match b with
    | [] => True
    | i :: bt => and (wftypes i) (wftypesb bt)
    end.

  Fixpoint wfvar (i : instruction) : Prop :=
    match i with
    | @assign ty i => and (isValue ty)
                          match i with
                          | assign3 _ v1 _ _ => isLval v1
                          | assign2 _ v1 _  => isLval v1
                          | update2 _ v1 _  => isLval v1
                          | update1 _ v1     => isLval v1
                          end
    end
  .

  Fixpoint wfvarb (b : block) : Prop :=
    match b with
    | [] => True
    | i :: bt => and (wfvar i) (wfvarb bt)
    end.


End Language.

Arguments wftypesb [var] _ .
Arguments wfvarb [var] _ .

Fixpoint striparg {var : type -> Type} {ty : type} (a : arg var ty) : Ensemble (sigT var) :=
  match a with
  | v _ vv => Singleton _ (existT var _ vv) 
  | constant _ c => Empty_set _
  | index _ arr => (striparg arr)
  end.

Fixpoint getvars {var : type -> Type} (b : block var) : Ensemble (sigT var) :=
  match b with
  | [] => Empty_set _
  | i :: bt => Union _ 
                     match i with
                     | assign _ ty a => match a with
                                        | assign3 _ _ a1 a2 a3 => Union _ (Union _ (striparg a1) (striparg a2)) (striparg a3)
                                        | assign2 _ _ a1 a2 => Union _ (striparg a1) (striparg a2)
                                        | update2 _ _ a1 a2 => Union _ (striparg a1) (striparg a2)
                                        | update1 _ _ a1 => striparg a1
                                        end
                     end
                     (getvars bt)
  end.

Fixpoint lifttrans {v1 : type -> Type} {v2 : type -> Type}  (transv : forall ty, v1 ty -> v2 ty) { ty : type} (a : (arg v1) ty) : (arg v2) ty :=
  match a with
                     | v _ vv1 => v _ (transv _ vv1)
                     | constant _ c => constant _ c
                     | @index _ b e ty (arr) => 
                       index _ (lifttrans transv arr)
  end.

Fixpoint translateb {v : type -> Type} {w : type -> Type} (transv : forall ty, v ty -> w ty) (b : list (instruction v)) {struct b} : block w :=
  match b with
  | [] => []
  | i :: bt => (fun i => match i with
                         | assign _ ty a => match a with
                                         | @assign3 _ _ b v1 v2 v3 => assign w _ (assign3 w b (lifttrans transv v1) (lifttrans transv v2) (lifttrans transv v3))
                                         | @assign2 _ _ u v1 v2 => assign w _ (assign2 w u (lifttrans transv v1) (lifttrans transv v2))
                                         | @update2 _ _ b v1 v2 => assign w _ (update2 w b (lifttrans transv v1) (lifttrans transv v2))
                                         | @update1 _ _ u v1 => assign w _ (update1 w u (lifttrans transv v1))
                                         end
                         end
               ) i :: (translateb transv bt)
  end.


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
(*Notation "'FOR' V 'IN' S 'DO' B" :=  (each V S B) (at level 20).*)

