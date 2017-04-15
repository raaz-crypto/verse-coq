Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Cat.
Require Import Verse.Syntax.
Require Vector.
Require Import List.
Require Import Coq.Sets.Ensembles.
Require Import Recdef.
Import String.
Require Import Basics.
Require Import Coq.Logic.FunctionalExtensionality.

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
    : v (array b e ty) -> arg ty.

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
   | indexIsLval {b : nat} {e : endian} {a : v (array b e ty)}: isLval (index a)
  .
  Definition wftypes (i : instruction) : Prop := True.

  Definition wftypesB (b : block) : Prop := fold_left and (map wftypes b) True.

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

Arguments wftypesB [v] _ .
Arguments wfvarB [v] _ .

Lemma casesOpt {T : Type} (o : option T) : {t : T | o = Some t} + {o = None}.
Proof.
  exact 
  match o with
  | Some t => inleft (exist _ t eq_refl)
  | None   => inright (eq_refl)
  end.
Qed.

(* Syntax modules *)

Module Arg <: VarTto VarT.

  Definition omap := arg.

  Definition mmap {v1 v2} (f : subT v1 v2) : subT (arg v1) (arg v2) :=
    fun ty a =>
    match a with
    | var  _ vv1 => var _ (f _ vv1)
    | constant _ c => constant _ c
    | index _ arr => index _ (f _ arr)
    end.

  Arguments mmap {v1 v2} _ [t] _.

  Lemma idF (u : varT) :  mmap (@VarT.idM u) = VarT.idM.
  Proof.
    crush_ast_obligations.
  Qed.

  Lemma functorial : forall {u v w} {g : subT v w} {f : subT u v}, mmap (g << f) = VarT.composeM (mmap g) (mmap f).
  Proof.
    crush_ast_obligations.
  Qed.

  Definition vSet {v} {ty} (a : omap v ty) : Ensemble (sigT v) :=
    match a with
    | (var _ vv) => Singleton _ (existT v _ vv) 
    | (constant _ c) => Empty_set _
    | (index _ arr) => Singleton _ (existT v _ arr)
    end.

  Definition usedIn {v} {ty} (o : omap v ty) (var : sigT v) := In _ (vSet o) var.
  Definition undef {v w} (f : opSubT v w) (var : sigT v) := f _ (projT2 var) = None.

  Arguments vSet / _ _ _ _ : simpl nomatch.
  Arguments usedIn / _ _ _ _.
  Arguments undef / _ _ _ _.

  Definition opt {v w : varT} {ty} (f : opSubT v w) (o : omap v ty) :=
    omap w ty + {exists var : sigT v, and (In _ (vSet o) var) (f _ (projT2 var) = None)}.


  Definition opmap {v w} {ty} (f : opSubT v w) (o : omap v ty) : opt f o.
    refine
      (match o with 
       | var _ vv => match casesOpt (f _ vv) with
                     | {- exist _ a _ -} => {- var _ a -}
                     | error p => error _
                     end
       | constant _ c => inleft (constant _ c)
       | index _ arr => match casesOpt (f _ arr) with
                        | {- exist _ a _ -} => {- index _ a -}
                        | error p => error _
                        end
       end).
    refine (ex_intro _ (existT _ _ vv) _); simpl; eauto.
    refine (ex_intro _ (existT _ _ arr) _); simpl; eauto.
  Qed.
    
End Arg.

Fixpoint striparg {var : varT} {ty : type} (a : arg var ty) : Ensemble (sigT var) :=
  match a with
  | var _ vv => Singleton _ (existT var _ vv) 
  | constant _ c => Empty_set _
  | index _ arr => Singleton _ (existT var _ arr)
  end.

Module Assignment <: AST.

  Definition syn  := assignment.
  Definition transform {v w} (f : subT v w) (a : assignment v) : assignment w :=
   match a with
   | @assign3 _ _ b v1 v2 v3 => assign3 w _ b (Arg.mmap f v1) (Arg.mmap f v2) (Arg.mmap f v3)
   | @assign2 _ _ u v1 v2 => assign2 w _ u (Arg.mmap f v1) (Arg.mmap f v2)
   | @update2 _ _ b v1 v2 => update2 w _ b (Arg.mmap f v1) (Arg.mmap f v2)
   | @update1 _ _ u v1 => update1 w _ u (Arg.mmap f v1)
   end.

  Definition omap := syn.
  Definition mmap := fun {v w} => @transform v w.

  Lemma idF {u} : mmap (@VarT.idM u) = id.
  Proof.
    Hint Rewrite Arg.idF.
    
    crush_ast_obligations.

  Qed. 

  Lemma functorial {u v w}{g : subT v w}{f : subT u v}: mmap (g << f) = TypeCat.composeM (mmap g) (mmap f).
  Proof.
    Hint Rewrite @Arg.functorial.

    crush_ast_obligations.
  Qed.

  Definition vSet {var} (a : omap var) : Ensemble (sigT var) :=
    match a with
    | assign3 _ _ _ a1 a2 a3 => Union _ (Union _ (Arg.vSet a1) (Arg.vSet a2)) (Arg.vSet a3)
    | assign2 _ _ _ a1 a2 => Union _ (Arg.vSet a1) (Arg.vSet a2)
    | update2 _ _ _ a1 a2 => Union _ (Arg.vSet a1) (Arg.vSet a2)
    | update1 _ _ _ a1 => Arg.vSet a1
    end.

  Definition usedIn {v} (o : omap v) (var : sigT v) := In _ (vSet o) var.
  Definition undef {v w} (f : opSubT v w) (var : sigT v) := f _ (projT2 var) = None.

  Arguments vSet / _ _ _ : simpl nomatch.
  Arguments usedIn / _ _ _.
  Arguments undef / _ _ _ _.
    
  Definition opt {v w : varT} (f : opSubT v w) (o : omap v) :=
    omap w + {exists var : sigT v, usedIn o var /\ undef f var}.

  Definition opmap {v1 w} (f : opSubT v1 w) (o : omap v1): opt f o.

    refine
      match o with
      | update1 _ _ u av => match Arg.opmap f av with
                            | {- aw -} => {- update1 _ _ u aw -}
                            | error p => error _
                            end
      | update2 _ _ u av1 av2 => match Arg.opmap f av1, Arg.opmap f av2 with
                                 | {- aw1 -}, {- aw2 -} => {- update2 _ _ u aw1 aw2 -}
                                 | error p, _ => error _ 
                                 | _, error p => error _ 
                                 end
      | assign3 _ _ u av1 av2 av3 => match Arg.opmap f av1, Arg.opmap f av2, Arg.opmap f av3 with
                                     | {- aw1 -}, {- aw2 -}, {- aw3 -} => {- assign3 _ _ u aw1 aw2 aw3 -}
                                     | error p, _, _ => error _ 
                                     | _, error p, _ => error _ 
                                     | _, _, error p => error _ 
                                     end
      | assign2 _ _ u av1 av2 => match Arg.opmap f av1, Arg.opmap f av2 with
                                 | {- aw1 -}, {- aw2 -} => {- assign2 _ _ u aw1 aw2 -}
                                 | error p, _ => error _ 
                                 | _, error p => error _ 
                                 end
      end;
    destruct p as [ pv pc ];
    destruct pc as [ pi pn ];
    refine (ex_intro _ pv _);
    cbv delta - [In]; eauto.

  Qed.
  
End Assignment.

Module Instruction <: AST.

  Definition syn := instruction.
  Definition transform {v w} (f : subT v w) (i : instruction v) : instruction w :=
  match i with
  | assign _ a => assign w (Assignment.mmap f a)
  end.


  Definition omap := syn.
  Definition mmap := fun {v w} => @transform v w.

  
  Lemma idF {u}: mmap (@VarT.idM u) = id.
  Proof.
    Hint Rewrite @Assignment.idF.
    
    crush_ast_obligations.
  Qed.    
    
  Lemma functorial {u v w}{g : subT v w}{f : subT u v}: mmap (g << f) = compose (mmap g) (mmap f).
  Proof.
    Hint Rewrite @Assignment.functorial.

    crush_ast_obligations.
  Qed.

  Definition vSet {var} (i : omap var) : Ensemble (sigT var) :=
    match i with
    | assign _ a => Assignment.vSet a
    end.


  Definition usedIn {v} (o : omap v) (var : sigT v) := In _ (vSet o) var.
  Definition undef {v w} (f : opSubT v w) (var : sigT v) := f _ (projT2 var) = None.

  Arguments vSet / _ _ _ : simpl nomatch.
  Arguments usedIn / _ _ _.
  Arguments undef / _ _ _ _.

  Definition opt {v w : varT} (f : opSubT v w) (o : omap v) :=
    omap w + {exists var : sigT v, usedIn o var /\ undef f var}.

  Definition opmap {v w} (f : opSubT v w) (o : omap v) : opt f o.
    refine
      match o with
      | assign _ iv => match Assignment.opmap f iv with
                       | {- iw -} => {- assign _ iw -}
                       | error p => error _ 
                       end
      end.
    destruct p as [pv pp].
    destruct pp as [pi pn].
    refine (ex_intro _ pv _).
    eauto.
    Qed.
  
End Instruction.

Module Block := ListAST Instruction.

(* Helper functions for the Function module *)

Fixpoint ivars {var} (i : instruction var) : Ensemble (sigT var) :=
  match i with
  | assign _ a => match a with
                     | assign3 _ _ _ a1 a2 a3 => Union _ (Union _ (striparg a1) (striparg a2)) (striparg a3)
                     | assign2 _ _ _ a1 a2 => Union _ (striparg a1) (striparg a2)
                     | update2 _ _ _ a1 a2 => Union _ (striparg a1) (striparg a2)
                     | update1 _ _ _ a1 => striparg a1
                     end
  end.

Definition bvars {var : varT} (b : block var) := fold_left (fun S i => Union _ S (ivars i)) b (Empty_set _).


(*
Definition alloc_not_none {v1 v2} (transv : forall ty, v1 ty -> option (v2 ty)) (i : instruction v1) (allAlloc : forall vv : sigT v1, In _ (ivars i) vv -> transv _ (projT2 vv) <> None)
  : instruction v2.
  refine (
      match i with
      | assign _ ty a => match a with
                         | @assign3 _ _ b v1 v2 v3 => assign w _ (assign3 w b (map_for_arg transv v1) (map_for_arg transv v2) (map_for_arg transv v3))
                         | @assign2 _ _ u v1 v2 => assign w _ (assign2 w u (map_for_arg transv v1) (map_for_arg transv v2))
                         | @update2 _ _ b v1 v2 => assign w _ (update2 w b (map_for_arg transv v1) (map_for_arg transv v2))
                         | @update1 _ _ u v1 => assign w _ (update1 w u (map_for_arg transv v1))
                         end
      end
*)

(*
Fixpoint translatem {v : type -> Type} {w : type -> Type} (transv : forall ty, v ty -> option (w ty)) (b : list (instruction v)) (allAlloc : forall vv : sigT v, In _ (getvars b) vv ->  transv _ (projT2 vv) <> None) : Prop := 
  refine (
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
(*Notation "'FOR' V 'IN' S 'DO' B" :=  (each V S B) (at level 20).*)

