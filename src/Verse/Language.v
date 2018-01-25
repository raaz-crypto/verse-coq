Require Import Verse.Types.Internal.
Require Import Verse.Types.
Require Import Verse.Syntax.

Require Import Bool.
Require Import Omega.
Require Vector.
Require Import List.
Require Import Coq.Sets.Ensembles.
Require Import Recdef.
Import String.
Require Import Basics.
Require Import Arith.
Import Nat.
Import ListNotations.

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

Most architectures allow various basic arithmetic and bitwise
operations on values stored in the registers. These operations can be
either [unary] or [binary].

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
| mov     : op unary
| nop     : op unary
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

  Variable v   : VariableT.



(** ** Arguments.

Each verse program fragment consists of instructions applied to some
arguments. Variables are one form of arguments, but so does indexed
arrays or constants.

*)
  Inductive arg : VariableT :=
  | var   : forall {k} {ty : type k}, v k ty -> arg k ty
  | const : forall {k} {ty : type k}, constant ty  -> arg k ty
  | index : forall {b : nat}{e : endian}{ty : type direct},
     v memory (array b e ty) -> {i : nat | i < b} -> arg direct ty.


  Section ArrayIndexing.

    Variable b : nat.
    Variable e : endian.
    Variable ty : type direct.
    (** Type that captures a memory variables indices. *)

    Definition Indices (_ : v memory (array b e ty)) : Set
      := { i : nat | i < b }.


    Local Definition ithIndex i : list { i | i < b} :=
      match lt_dec i b with
      | left pf => [exist _ i pf]
      | right _ => []
      end.


    Local Fixpoint loopover i :=
      match i with
      | 0   => []
      | S j => loopover j
      end ++ ithIndex i.

    Definition indices (a : v memory (array b e ty)) :  list (Indices a)
      := loopover b.

    Definition indices_reversed a := List.rev (indices a).

  End ArrayIndexing.

  (** ** Assignment statement.

      One of the most important class of statement is the assignment
      statement. The following inductive type captures assignment statement.

   *)
  Inductive assignment : Type :=
  | assign3
    : forall ty, binop -> arg direct ty -> arg direct ty -> arg direct ty -> assignment
  (** e.g. x = y + z *)
  | assign2
    : forall ty, uniop -> arg direct ty -> arg direct ty -> assignment (** e.g. x = ~ y   *)
  | update2
    : forall ty, binop -> arg direct ty -> arg direct ty -> assignment (** e.g. x += y    *)
  | update1
    : forall ty, uniop -> arg direct ty -> assignment          (** e.g. x ~= x    *)
  .

(**

Finally we have instructions that forms the basic unit of a program. A
program block is merely a list of instructions.

*)
  Inductive instruction : Type :=
  | assign : assignment -> instruction
  .

  Definition argErr i :=
    match i with
    | assign e => match e with
                  | assign3 _ _ (const _) _ _ 
                  | assign2 _ _ (const _) _   
                  | update2 _ _ (const _) _   
                  | update1 _ _ (const _)
                  | assign2 _ mov (var _) _   => true
                  | _                         => false
                  end
    end.


  Let isEndian {k} {ty} (nHostE : endian) (a : arg k ty) :=
    let eqEndb (e f : endian) : bool :=
        match e, f with
        | littleE, littleE
        | bigE, bigE       => true
        | _, _             => false
        end
    in
    match a  with
    | @index _ ne _ _ _ => eqEndb ne nHostE
    | _                 => false
    end.

  (** Function to check if a non-mov/store instruction uses arrays of offending endianness.
      Passing hostE as parameter allows all arrays. **)

  Definition endianError (nHostE : endian) (i : instruction) :=
    match i with
    | assign e  => match e with
                   | assign2 _ mov _ _
                   | assign2 _ nop _ _    => false
                   | assign3 _ _ a1 a2 a3 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3)
                   | assign2 _ _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update2 _ _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update1 _ _ a1       => (isEndian nHostE a1)
                   end
    end
  .
  
  Definition supportedInst (nhostE : endian) := fun i =>
                                                  (argErr i = false
                                                   /\
                                                   endianError nhostE i = false).

  Definition instCheck e i : {supportedInst e i} + {~ supportedInst e i}.
    unfold supportedInst.
    assert (lval_dec := bool_dec (argErr i) false).
    assert (endian_dec := bool_dec (endianError e i) false).
    destruct lval_dec.
    destruct endian_dec.
    all: solve
           [constructor 1; repeat (constructor; trivial) | constructor 2; unfold not; intros; destruct H; contradiction].
  Defined.

  Definition block := list instruction.


  Definition foreach {b : nat}(ixs : list {ix | ix < b}) (f : forall ix, ix < b -> block) :  block :=
    let mapper := fun ix => match ix with
                            | exist _ i pf => f i pf
                            end
    in List.concat (List.map mapper ixs).



End Language.


Arguments Indices [v b e ty] _.
Arguments indices [v b e ty] _.
Arguments foreach [v b] _ _.
(*
Arguments foreach [v bound ty e] _ _.
Arguments foreachIndex [v bound ty e] _ _.


Definition foreach v bound ty e A loop := foreachIndex
Variable loopbody  : arg direct ty -> block.

*)
(* The body of an iterator over a sequence of blocks of type [ty] *)
Record iterator (ty : type memory)(v : VariableT) := Record { setup    : block v;
                                                         process  : v memory ty -> block v;
                                                         finalise : block v
                                                       }.


(* begin hide *)
Arguments setup [ty v] _.
Arguments process [ty v] _ _.
Arguments finalise [ty v] _.

Arguments var [v k ty] _ .
Arguments const [v k ty] _ .
Arguments index [v b e ty]  _ _.
Arguments assign3 [v ty] _ _ _ _ .
Arguments assign2 [v ty] _ _ _ .
Arguments update2 [v ty] _ _ _ .
Arguments update1 [v ty] _ _ .
Arguments assign [v] _ .

(* end hide *)

(** ** Notation.

A user is expected to define a program by giving a list of
[instruction]s. Expressing instructions directly using the
constructors of the [arg] and [instruction] types can be painful. We
expose some convenient notations for simplifying this task. Note that
in the notations below, the operands of the instruction can either be
variables or constants or indexed arrays.

 *)

(* begin hide *)

Class ARG (v : VariableT)(k : kind)(ty : type k) t  := { toArg : t -> arg v k ty }.

(** Instances of this class has been defined for both variables and constants *)


Section ARGInstances.
  Variable v  : VariableT.
  Variable k  : kind.
  Variable ty : type k .

  Global Instance arg_of_arg  : ARG v k ty (arg v k ty) := { toArg := fun x => x  }.
  Global Instance arg_of_v    : ARG v k ty (v k ty)     := { toArg := @var v k ty   }.
  Global Instance const_arg_v : ARG v k ty (Types.constant ty) := { toArg := @const v k ty }.

End ARGInstances.

(* end hide *)

Notation "A [- N -]"     := (index A (exist _ (N%nat) _)) (at level 69).
Notation "! A"           := (index A 0 _) (at level 70).
Notation "A ::= B [+] C" := (assign (assign3 plus  (toArg A) (toArg B) (toArg C) ))  (at level 70).

Notation "A ::= B [-] C" := (assign (assign3 minus (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A ::= B [*] C" := (assign (assign3 mul   (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A ::= B [/] C" := (assign (assign3 quot  (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A ::= B [%] C" := (assign (assign3 rem   (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A ::= B [|] C" := (assign (assign3 bitOr (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A ::= B [&] C" := (assign (assign3 bitAnd (toArg A) (toArg B) (toArg C)))  (at level 70).
Notation "A ::= B [^] C" := (assign (assign3 bitXor (toArg A) (toArg B) (toArg C)))  (at level 70).

Notation "A ::=+ B " := (assign (update2 plus  (toArg A) (toArg B))) (at level 70).
Notation "A ::=- B " := (assign (update2 minus (toArg A) (toArg B))) (at level 70).
Notation "A ::=* B " := (assign (update2 mul   (toArg A) (toArg B))) (at level 70).
Notation "A ::=/ B " := (assign (update2 quot  (toArg A) (toArg B))) (at level 70).
Notation "A ::=% B " := (assign (update2 rem   (toArg A) (toArg B))) (at level 70).
Notation "A ::=| B " := (assign (update2 bitOr   (toArg A) (toArg B))) (at level 70).
Notation "A ::=& B " := (assign (update2 bitAnd   (toArg A) (toArg B))) (at level 70).
Notation "A ::=^ B " := (assign (update2 bitXor   (toArg A) (toArg B))) (at level 70).

Notation "A ::=~ B "     := (assign (assign2 bitComp    (toArg A) (toArg B))) (at level 70).
Notation "A ::= B <*< N" := (assign (assign2 (rotL N)   (toArg A) (toArg B))) (at level 70).
Notation "A ::= B >*> N" := (assign (assign2 (rotR N)   (toArg A) (toArg B))) (at level 70).
Notation "A ::= B <<  N"  := (assign (assign2 (shiftL N) (toArg A) (toArg B))) (at level 70).
Notation "A ::= B >>  N" := (assign (assign2 (shiftR N) (toArg A) (toArg B))) (at level 70).
Notation "A ::=<< N "    := (assign (update1 (shiftL N) (toArg A))) (at level 70).
Notation "A ::=>> N "    := (assign (update1 (shiftR N) (toArg A))) (at level 70).
Notation "A ::=<*< N "    := (assign (update1 (rotL N) (toArg A))) (at level 70).
Notation "A ::=>*> N "    := (assign (update1 (rotR N) (toArg A))) (at level 70).

Notation "A ::== B"      := (assign (assign2 nop (toArg A) (toArg B))) (at level 70).
Notation "A <== B"       := (assign (assign2 mov (toArg A) (toArg B))) (at level 70).

(**

One another irritant in writing code is that the array indexing needs
proof that the bounds are not violated. We use the following tactic to
dispose off all such obligations.

*)

Tactic Notation "body" uconstr(B) := (refine B; omega).



(** *** Illustrative example of the notation.

To demonstrate the use of this notation, we first an inductive type
whose constructors are the variables of our program.

*)

Inductive MyVar : VariableT :=
|  X : MyVar direct Word8
|  Y : MyVar direct Word64
|  Z : MyVar direct (Vector128 Word32)
|  A : MyVar memory (array 42 bigE Word8)
.


(**

For illustration consider the following (nonsensical) program
fragment.  Notice that we can directly use the variables (as in [X],
[Y], Z) or constants (the [Ox "..."] are appropriate constants) as
operands of the programming fragment.


 *)





Require Vector.
Import  Vector.VectorNotations.
Require Import Verse.Word.

Definition vec_const : constant (Vector128 Word32) := [ Ox "12345678"; Ox "12345678"; Ox "12345678"; Ox "12345678"].

Definition prog : block MyVar.
  body [ X ::= X << 5 ;
         X ::=>> 5;
         X ::= X [+] (A[- 2 -]);
         X ::= X [+] Ox "55";
         Z ::= Z [+] vec_const
       ]%list.
Defined.




Require Import Verse.PrettyPrint.

(** ** Pretty printing of verse instructions.

It is convenient to have a pretty printed syntax for instructions in
verse. Since instructions are parameterised by variables, we give a
C-like pretty printing for verse instructions defined over variables
that can themselves be pretty printed. We start by defining a section
for this where we parameterise over teh variable type and its pretty
printing instance.


*)

(* begin hide *)
Section PrettyPrintingInstruction.

  (** The variable type for our instructions *)
  Variable v : VariableT.


  (** The pretty printing instance for our variable *)
  Variable vPrint : forall k ty, PrettyPrint (v k ty).

  (** The pretty printing of our argument *)
  Fixpoint argdoc {k}(ty : type k ) (av : arg v k ty) :=
    match av with
    | var v       => doc v
    | const c     => doc c
    | index v (exist _ n _) => doc v <> bracket (decimal n)
    end.

  Global Instance arg_pretty_print : forall k ty, PrettyPrint (arg v k ty)
    := { doc := argdoc ty }.

  Definition opDoc {a : arity}(o : op a) :=
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
    | mov      => text ""
    | nop      => text ""
    end.

  Definition EQUALS := text "=".
  Definition mkAssign {a : arity}(o : op a)   (x y z : Doc)  := x <_> EQUALS <_> y <_> opDoc o <_> z.
  Definition mkRot    {k}(ty : type k)(o : op unary) (x y : Doc)  :=
    let rotSuffix := match ty with
                     | word w     => decimal (2 ^ (w + 3))%nat
                     | multiword v w => text "V" <> decimal (2^v * 2^(w+3)) <> text "_" <> decimal (2^(w +3))
                     | _          => text "Unsupported"
                     end in
    match o with
    | rotL n => x <_> EQUALS <_> text "rotL" <> rotSuffix <> paren (commaSep [y ; decimal n])
    | rotR n => x <_> EQUALS <_> text "rotR" <> rotSuffix <> paren (commaSep [y ; decimal n])
    | _      => text "BadOp"
    end.

  Definition mkUpdate {a : arity}(o : op a) (x y   : Doc) := x <_> opDoc o <> EQUALS <_> y.

  (** The pretty printing of assignment statements **)
  Global Instance assignment_pretty_print : PrettyPrint (assignment v)
    := { doc := fun assgn =>  match assgn with
                              | assign3 o x y z => mkAssign o (doc x) (doc y) (doc z)
                              | update2 o x y   => mkUpdate o (doc x) (doc y)
                              | @assign2 _ ty u x y   =>
                                match u with
                                | bitComp  | nop | mov => mkAssign u (doc x) empty (doc y)
                                | shiftL n | shiftR n  => mkAssign u (doc x) (doc y) (decimal n)
                                | rotL n   | rotR n    => mkRot ty u (doc x)(doc y)
                                end
                              | @update1 _ ty u x      =>
                                match u with
                                | bitComp  | nop | mov => mkAssign u (doc x) empty (doc x)
                                | shiftL n | shiftR n  => mkUpdate u (doc x) (decimal n)
                                | rotL n   | rotR n    => mkRot ty u (doc x) (doc x)
                                end
                              end
       }.

  Global Instance instruction_pretty_print : PrettyPrint (instruction v)
    := { doc := fun i => match i with
                         | assign a => doc a
                         end
       }.

End PrettyPrintingInstruction.

(* end hide *)





(**

To get the above program frgment pretty printed all we need is pretty
print instance for the variable type [MyVar].

*)

Instance PrettyPrintMyVar : forall k ty, PrettyPrint (MyVar k ty) :=
  { doc := fun v => text ( match v with
                           | X => "X"
                           | Y => "Y"
                           | Z => "Z"
                           | A => "A"
                           end
                         )
  }.


(** The above program fragment is pretty printable because the
underlying variable type ([MyVar] in this case), is pretty printable
 *)

Compute layout (doc prog).