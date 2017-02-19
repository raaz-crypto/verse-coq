Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Syntax.
Require Vector.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.
Require Import Recdef.
Import String.
Require Import Basics.
Require Import FunctionalExtensionality.

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

(* Syntax modules *)

Fixpoint map_for_arg {v1 v2} (transv : subT v1 v2) {ty : type} (a : (arg v1) ty) : (arg v2) ty :=
  match a with
                     | v _ vv1 => v _ (transv _ vv1)
                     | constant _ c => constant _ c
                     | @index _ b e ty (arr) => 
                       index _ (map_for_arg transv arr)
  end.

Lemma identity_for_arg : forall (ty : type) (u : varT) (v : arg u ty), @map_for_arg u u (idSubst u) ty v = id v.
Proof.
  intros.
  induction v0; eauto.
  unfold id.
  unfold map_for_arg. f_equal.
  eauto.
Qed.

Lemma composition_for_arg : forall {ty : type}{u v w}{g : subT v w} {f : subT u v}, compose (@map_for_arg _ _ g ty) (@map_for_arg _ _ f ty) = map_for_arg (g << f).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold compose.
  induction x; eauto.
  simpl.
  f_equal.
  eauto.
Qed.
  
Module Assignment <: AST.
  
  Definition syn := assignment.
  Definition map v w (transv : subT v w) (a : assignment v) : assignment w :=
    match a with
    | @assign3 _ _ b v1 v2 v3 => assign3 w _ b (map_for_arg transv v1) (map_for_arg transv v2) (map_for_arg transv v3)
    | @assign2 _ _ u v1 v2 => assign2 w _ u (map_for_arg transv v1) (map_for_arg transv v2)
    | @update2 _ _ b v1 v2 => update2 w _ b (map_for_arg transv v1) (map_for_arg transv v2)
    | @update1 _ _ u v1 => update1 w _ u (map_for_arg transv v1)
    end.

  Arguments map [v w] _ _.

  Lemma identity {u}: map (idSubst u) = id.
  Proof.
    Hint Rewrite identity_for_arg.
    unfold map.
        
    crush_ast_obligations. 
  Qed. 

  Lemma composition {u v w}{g : subT v w}{f : subT u v}: compose (map g) (map f) = map (g << f).
  Proof.
    Hint Rewrite <- @composition_for_arg.

    intros.
    unfold map.

    crush_ast_obligations.
  Qed.
  
End Assignment.

Module Instruction <: AST.

  Import Assignment.
  Definition syn := instruction.
  Definition map v w (transv : subT v w) (i : instruction v) : instruction w :=
  match i with
  | assign _ a => assign w (map transv a)
  end.

  Arguments map [v w] _ _.
  
  Lemma identity {u}: map (idSubst u) = id.
  Proof.
    Hint Rewrite identity_for_arg.
    Hint Rewrite @Assignment.identity.
    
    unfold map.
    crush_ast_obligations.
  Qed.    
    
  Lemma composition {u v w}{g : subT v w}{f : subT u v}: compose (map g) (map f) = map (g << f).
  Proof.
    Hint Rewrite <- @Assignment.composition.

    intros.
    unfold map.
    crush_ast_obligations.
  Qed.

End Instruction.

Module Block := ListAST Instruction.


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

