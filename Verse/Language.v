Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Syntax.
Require Vector.
Require Import List.
Require Import Coq.Sets.Ensembles.
Require Import Recdef.
Import String.
Require Import Basics.

(** * The Verse language as an inductive data type.

This module exposes the abstract syntax of the verse programming
language. The design takes the following points into consideration.

- A large number of instructions are shared across architectures. This
  include instructions that perform various arithmetic operations,
  bitwise operations etc.

- Certain architecture support various special registers like xmm
  registers, special instructions like native AES operations.

The design gives a portable way of expressing the former and
parameterise over the latter. We start with defining the various built
in operators that verse support.

** Arithmetic and bitwise operators.

Most architectures allow various basic arithmetic, bitwise operations
on values stored in the registers. These instructions can be of arity
unary or binary.

*)

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

(**

This section build up towards the the inductive type that capture the
verse language's abstract syntax tree. One of the most important
elements in a programming language is variables. In verse, program
fragments are parameterised by an abstract variable type that is used
through out.

*)

  Variable v   : varT.



(** ** Arguments.

Each verse program fragment consists of instructions applied to some
arguments. Variables are one form of arguments, the other are
constants or indexed variables. The type arg captures this.

*)


  Inductive arg : type -> Type :=
  | var      {ty : type} : v ty -> arg ty
  | const {ty : type} : constant ty  -> arg ty
  | index {b : nat}{e : endian}{ty : type}
    : v (array b e ty) -> nat -> arg ty.



  (** ** Assignment statement.

      One of the most important class of statement is the assignment
      statement. The following inductive type captures assignment statement.

   *)
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

(**

Finally we have instructions that forms the basic unit of a program. A
program block is merely a list of instructions.

*)
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
                  | assign2 ty _ v1 _   => and (isValue ty) (isLval v1)
                  | update2 ty _ v1 _   => and (isValue ty) (isLval v1)
                  | update1 ty _ v1     => and (isValue ty) (isLval v1)
                  end
    end.

  Definition wfvarB (b : block) : Prop := fold_left and (map wfvar b) True.

End Language.


Arguments var [v ty] _ .
Arguments const [v ty] _ .
Arguments index [v b e ty] _ _ .
Arguments assign3 [v ty] _ _ _ _ .
Arguments assign2 [v ty] _ _ _ .
Arguments update2 [v ty] _ _ _ .
Arguments update1 [v ty] _ _ .
Arguments assign [v] _ .
Arguments wfvarB [v] _ .



(** * Pretty Notation.

Expressing instructions directly as elements of the instruction type
is painful. The first painful aspect comes from explictly having to
lift each variable and constant to the argument level. This we solve
using the following class.

*)

Class ARG (v : varT) (ty : type) t  := { toArg : t -> arg v ty }.

(** Instances of this class has been defined for both variables and constants *)

Section ARGInstances.
  Variable v  : varT.
  Variable ty : type.

  Global Instance arg_of_arg  : ARG v ty (arg v ty) := { toArg := fun x => x  }.
  Global Instance arg_of_v    : ARG v ty (v ty)     := { toArg := @var v ty   }.
  Global Instance const_arg_v : ARG v ty (Types.constant ty) := { toArg := @const v ty }.

End ARGInstances.

Notation "A [- N -]"     := (index A N) (at level 69).
Notation "! A"           := (index A 0) (at level 70).
Notation "A <= B <+> C " := (assign (assign3 plus  (toArg A) (toArg B) (toArg C) ))  (at level 70).

Notation "A <= B <-> C " := (assign (assign3 minus (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A <= B <*> C" := (assign (assign3 mul   (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A <= B </> C " := (assign (assign3 quot  (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A <= B <%> C " := (assign (assign3 rem   (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A <= B <|> C " := (assign (assign3 rem   (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A <= B <&> C " := (assign (assign3 rem   (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A <= B <^> C " := (assign (assign3 rem   (toArg A) (toArg B) (toArg C)))  (at level 70).

Notation "A <=+ B " := (assign (update2 plus  (toArg A) (toArg B))) (at level 70).
Notation "A <=- B " := (assign (update2 minus (toArg A) (toArg B))) (at level 70).
Notation "A <=* B " := (assign (update2 mul   (toArg A) (toArg B))) (at level 70).
Notation "A <=/ B " := (assign (update2 quot  (toArg A) (toArg B))) (at level 70).
Notation "A <=% B " := (assign (update2 rem   (toArg A) (toArg B))) (at level 70).
Notation "A <=| B " := (assign (update2 bitOr   (toArg A) (toArg B))) (at level 70).
Notation "A <=& B " := (assign (update2 bitAnd   (toArg A) (toArg B))) (at level 70).
Notation "A <=^ B " := (assign (update2 bitXor   (toArg A) (toArg B))) (at level 70).

Notation "A <=~ B "     := (assign (assign2 bitComp    (toArg A) (toArg B))) (at level 70).
Notation "A <= B <*< N" := (assign (assign2 (rotL N)   (toArg A) (toArg B))) (at level 70).
Notation "A <= B >*> N" := (assign (assign2 (rotR N)   (toArg A) (toArg B))) (at level 70).
Notation "A <= B <<  N"  := (assign (assign2 (shiftL N) (toArg A) (toArg B))) (at level 70).
Notation "A <= B >>  N" := (assign (assign2 (shiftR N) (toArg A) (toArg B))) (at level 70).
Notation "A <=<< N "    := (assign (update1 (shiftL N) (toArg A))) (at level 70).
Notation "A <=>> N "    := (assign (update1 (shiftR N) (toArg A))) (at level 70).
Notation "A <=<*< N "    := (assign (update1 (rotL N) (toArg A))) (at level 70).
Notation "A <=>*> N "    := (assign (update1 (rotR N) (toArg A))) (at level 70).


Require Import Verse.Word.

(** * Example using this notation.

To demonstrate the use of this notation we first define a inductive
type to capture variables.

*)

Inductive MyVar : varT :=
|  X : MyVar Word8
|  Y : MyVar Word64
|  A : MyVar (ArrayT 42 bigE Word8)
.

Import ListNotations.
Definition prog : block MyVar  := [ X <= X <+> A[-2-]; X <= X << 5 ; X <=>> 5].


Require Import Verse.PrettyPrint.

(** * Pretty printing of verse instructions.

It is convenient to have a pretty printed syntax for instructions in
verse. Since instructions are parameterised by variables, we give a
C-like pretty printing for verse instructions. We start by defining a
section for this where we parameterise over teh variable type and its
pretty printing instance.


*)

Section PrettyPrintingInstruction.

  (** The variable type for our instructions *)
  Variable v : varT.


  (** The pretty printing instance for our variable *)
  Variable vPrint : forall ty : type, PrettyPrint (v ty).

  (** The pretty printing of our argument *)
  Global Instance arg_pretty_print : forall ty, PrettyPrint (arg v ty)
    := { doc := fun av => match av with
                          | var v      => doc v
                          | const c    => doc c
                          | index v n  => doc v <> bracket (decimal n)
                          end
       }.

  Local Definition opDoc {a : arity}(o : op a) :=
    match o with
    | plus     => text "+"
    | minus    => text "-"
    | mul      => text "*"
    | quot     => text "/"
    | rem      => text "%"
    | bitOr    => text "|"
    | bitAnd   => text "&"
    | bitXor   => text "^"
    | bitComp  => text "~"
    | rotL _   => text "<*<"
    | rotR _   => text ">*>"
    | shiftL _ => text "<<"
    | shiftR _ => text ">>"
    end.

  Local Definition EQUALS := text "=".
  Local Definition mkAssign {a : arity}(o : op a) (x y z : Doc) := x <_> EQUALS <_> y <_> opDoc o <_> z.
  Local Definition mkUpdate {a : arity}(o : op a) (x y   : Doc) := x <_> opDoc o <> EQUALS <_> y.

  (** The pretty printing of assignment statements **)
  Global Instance assignment_pretty_print : PrettyPrint (assignment v)
    := { doc := fun assgn =>  match assgn with
                              | assign3 o x y z => mkAssign o (doc x) (doc y) (doc z)
                              | update2 o x y   => mkUpdate o (doc x) (doc y)
                              | assign2 u x y   =>
                                match u with
                                | bitComp  => mkAssign u (doc x) empty (doc y)
                                | shiftL n
                                | shiftR n
                                | rotL n
                                | rotR n   => mkAssign u (doc x) (doc y) (decimal n)
                                end
                              | update1 u x      =>
                                match u with
                                | bitComp => mkAssign u (doc x) empty (doc x)
                                | shiftL n | shiftR n
                                | rotL n   | rotR n
                                             => mkUpdate u (doc x) (decimal n)
                                                   end
                              end
       }.

  Global Instance instruction_pretty_print : PrettyPrint (instruction v)
    := { doc := fun i => match i with
                         | assign a => doc a
                         end
       }.

End PrettyPrintingInstruction.

(** ** Example pretty printing

Let us define pretty printing instance for the variable above to demonstrate the use of
this pretty printing

 *)

Instance PrettyPrintMyVar : forall ty : type, PrettyPrint (MyVar ty) :=
  { doc := fun v => text ( match v with
                           | X => "X"
                           | Y => "Y"
                           | A => "A"
                           end
                         )
  }.
