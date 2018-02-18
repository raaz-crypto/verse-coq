(* begin hide *)
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Bool.
Require Import Omega.
Require Import List.
Import ListNotations.

(* end hide *)

(** * The Verse language as an inductive data type.

This module exposes the abstract syntax of the verse programming
language. The design takes the following points into consideration.

- A large number of instructions are shared across architectures. This
  include instructions that perform various arithmetic operations,
  bitwise operations etc.

- Certain architecture support various special registers like xmm
  registers, special instructions like native AES operations.

The design gives a portable way of expressing the former and
parameterise over the latter. Let us include arithmetic operators
first.

*)

Require Export Verse.Language.Operators.


(** * The abstract syntax tree.

This section build up towards the the inductive type that capture the
verse language's abstract syntax tree. One of the most important
elements in a programming language is variables. In verse, program
fragments are parameterised by an abstract variable type that is used
through out.

*)

Section Language.
  Variable v   : VariableT.


  (** Type that captures a memory variables indices. *)
  Definition Indices {b e ty} (_ : v memory (array b e ty)) := { i : nat | i < b }.


  (** ** Arguments.

      Each verse program fragment consists of instructions applied to
      some arguments. Variables are one form of arguments, but so does
      indexed arrays or constants.

   *)

  Inductive argKind := lval | rval.
  Inductive arg : argKind -> VariableT :=
  | var   : forall aK, forall {k} {ty : type k}, v k ty -> arg aK k ty
  | const : forall {ty : type direct}, constant ty  -> arg rval direct ty
  | index : forall aK, forall {b : nat}{e : endian}{ty : type direct} (x : v memory (array b e ty)),
        Indices x  -> arg aK direct ty
  .

  Definition larg := arg lval.
  Definition rarg := arg rval.



  (** ** Assignment statement.

      One of the most important class of statement is the assignment
      statement. The following inductive type captures assignment statement.

   *)
  Inductive assignment : Type :=
  | assign3
    : forall ty, binop -> larg direct ty -> rarg direct ty -> rarg direct ty -> assignment
  (** e.g. x = y + z *)
  | assign2
    : forall ty, uniop -> larg direct ty -> rarg direct ty -> assignment (** e.g. x = ~ y   *)
  | update2
    : forall ty, binop -> larg direct ty -> rarg direct ty -> assignment (** e.g. x += y    *)
  | update1
    : forall ty, uniop -> larg direct ty -> assignment                   (** e.g. x ~= x    *)
  .

(**

Finally we have instructions that forms the basic unit of a program. A
program block is merely a list of instructions.

*)
  Inductive instruction : Type :=
  | assign  : assignment -> instruction
  | moveTo  : forall b e ty, forall (x : v memory (array b e ty)), Indices x -> v direct ty -> instruction
  | destroy : forall {k ty}, v k ty -> instruction
  .

  Definition block := list instruction.

  (* begin hide *)

  (* Some instruction error checking code *)

  Let isEndian {aK} {k} {ty} (nHostE : endian) (a : arg aK k ty) :=
    let eqEndb (e f : endian) : bool :=
        match e, f with
        | littleE, littleE
        | bigE, bigE       => true
        | _, _             => false
        end
    in
    match a  with
    | @index _ _ ne _ _ _ => eqEndb ne nHostE
    | _                 => false
    end.

  (** Function to check if a non-mov/store instruction uses arrays of offending endianness.
      Passing hostE as parameter allows all arrays. **)

  Definition endianError (nHostE : endian) (i : instruction) :=
    match i with
    | assign e  => match e with
                   | assign2 _ nop _ _    => false
                   | assign3 _ _ a1 a2 a3 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3)
                   | assign2 _ _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update2 _ _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update1 _ _ a1       => (isEndian nHostE a1)
                   end
    | _ => false
    end
  .

  Definition supportedInst (nhostE : endian) := fun i => endianError nhostE i = false.

  Definition instCheck e i : {supportedInst e i} + {~ supportedInst e i}
      := bool_dec (endianError e i) false.

  (* end hide *)



End Language.

Arguments Indices [v b e ty] _.

(**

Many cryptographic primitives work on streams of data that are divided
into chunks of fixed size. The record [iterator] is essentially the
body of the an iterator that works with such a stream of blocks of
type [ty].

*)
Record iterator (ty : type memory)(v : VariableT)
  := Record { setup    : block v;
              process  : v memory ty -> block v;
              finalise : block v
            }.


(* begin hide *)
Arguments setup [ty v] _.
Arguments process [ty v] _ _.
Arguments finalise [ty v] _.

Arguments var [v aK k ty] _ .
Arguments const [v ty] _ .
Arguments index [v aK b e ty]  _ _.
Arguments assign3 [v ty] _ _ _ _ .
Arguments assign2 [v ty] _ _ _ .
Arguments update2 [v ty] _ _ _ .
Arguments update1 [v ty] _ _ .
Arguments assign [v] _ .
Arguments moveTo [v b e ty] _ _ _.
Arguments destroy [v k ty ] _.
(* end hide *)


(** ** Helper functions.

When working with verse we often need to write repetitive coding
patterns. This section documents some helper functions to facilitate
refactoring such code. Once can think of such helpers as "assembler
macros" and one of the advantage of using a DSL is that such "macros"
can be implemented in the host language; coq in this case.

 *)

(** *** Array indexing

The first set of helper functions gives convenient ways to work with
array indices. One of the most important operations is to perform
certain tasks for each element of the array. The [foreach] function
can be used for this. The first argument of the [foreach] function is
the list of indices of the array and its second argument is a function
that takes an index and generates some instructions.  Let [A] be an
array variable, then the function [indices A] gives such a list in
increasing order starting from 0.  One can think of the [foreach
(indices A) doSomethingWithIndex] as an unrolled loop that does some
computation on every index of A. If one wants to perform such a loop
in the reverse order on can use the function [indices_reversed]
instead of [indices].

*)

Section ArrayIndexing.

  Variable v   : VariableT.
  Variable b : nat.
  Variable e : endian.
  Variable ty : type direct.

  (* begin hide *)
  Local Definition ithIndex i : list { i | i < b} :=
    match lt_dec i b with
    | left pf => [exist _ i pf]
    | right _ => []
    end.


  Local Fixpoint loopover i :=
    (match i with
     | 0   => []
     | S j => loopover j
     end ++ ithIndex i)%list.

  (* end hide *)

  (**
     This function returns the list of valid indices of an array
     variable. The indices are given starting from [0] to [b -
     1]. Mostly used in conjunction with [foreach]

   *)
  Definition indices (a : v memory (array b e ty)) :  list (Indices a)
    := loopover b.

  (** This function is similar to indices but gives the indices in the
      reverse order.  *)
  Definition indices_reversed a := List.rev (indices a).


  (**
      This function allows mapping over all the input indices.

      <<
      foreach (indices A) statementsToTransformIthValue

      >>

   *)

  Definition foreach (ixs : list {ix | ix < b})
             (f : forall ix, ix < b -> block v)
    := let mapper := fun ix => match ix with
                               | exist _ i pf => f i pf
                               end
       in List.concat (List.map mapper ixs).

End ArrayIndexing.

(* begin hide *)

Arguments indices [v b e ty] _.
Arguments foreach [v b] _ _.

(* end hide *)

(** * Notation and Pretty printing.


A user is expected to define a program by giving a list of
[instruction]s. Expressing instructions directly using the
constructors of the [arg] and [instruction] types can be painful. We
expose some convenient notations for simplifying this task. Note that
in the notations below, the operands of the instruction can either be
variables or constants or indexed arrays.

It is convenient to have a pretty printed syntax for instructions in
verse. We give a C-like pretty printing for verse instructions defined
over variables that can themselves be pretty printed.

*)




(* begin hide *)


Class LARG (v : VariableT)(k : kind)(ty : type k) t  := { toLArg : t -> arg v lval k ty }.
Class RARG (v : VariableT)(k : kind)(ty : type k) t  := { toRArg : t -> arg v rval k ty }.

Section ARGInstances.
  Variable v  : VariableT.
  Variable k  : kind.
  Variable ty : type k .

  Global Instance larg_of_argv : LARG v k ty (arg v lval k ty) := { toLArg := fun t => t} .
  Global Instance rarg_of_argv : RARG v k ty (arg v rval k ty) := { toRArg := fun t => t}.
  Global Instance larg_of_v    : LARG v k ty (v k ty)    := { toLArg := fun t => var t}.
  Global Instance rarg_of_v    : RARG v k ty (v k ty)    := { toRArg := fun t => var t}.


End ARGInstances.

Global Instance const_arg_v (v : VariableT)(ty : type direct) : RARG v direct ty (Types.constant ty)
  := { toRArg := @const v ty }.

(* end hide *)



Notation "A [- N -]"     := (index A (exist _ (N%nat) _)) (at level 69).
Notation "! A"           := (index A 0 _) (at level 70).
Notation "A ::= B [+] C" := (assign (assign3 plus  (toLArg A) (toRArg B) (toRArg C) ))  (at level 70).

Notation "A ::= B [-] C" := (assign (assign3 minus (toLArg A) (toRArg B) (toRArg C)))  (at level 70).
Notation "A ::= B [*] C" := (assign (assign3 mul   (toLArg A) (toRArg B) (toRArg C)))  (at level 70).
Notation "A ::= B [/] C" := (assign (assign3 quot  (toLArg A) (toRArg B) (toRArg C)))  (at level 70).
Notation "A ::= B [%] C" := (assign (assign3 rem   (toLArg A) (toRArg B) (toRArg C)))  (at level 70).
Notation "A ::= B [|] C" := (assign (assign3 bitOr (toLArg A) (toRArg B) (toRArg C)))  (at level 70).
Notation "A ::= B [&] C" := (assign (assign3 bitAnd (toLArg A) (toRArg B) (toRArg C)))  (at level 70).
Notation "A ::= B [^] C" := (assign (assign3 bitXor (toLArg A) (toRArg B) (toRArg C)))  (at level 70).

Notation "A ::=+ B " := (assign (update2 plus  (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=- B " := (assign (update2 minus (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=* B " := (assign (update2 mul   (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=/ B " := (assign (update2 quot  (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=% B " := (assign (update2 rem   (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=| B " := (assign (update2 bitOr (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=& B " := (assign (update2 bitAnd (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=^ B " := (assign (update2 bitXor (toLArg A) (toRArg B))) (at level 70).

Notation "A ::=~ B "     := (assign (assign2 bitComp    (toLArg A) (toRArg B))) (at level 70).
Notation "A ::= B <*< N" := (assign (assign2 (rotL N)   (toLArg A) (toRArg B))) (at level 70).
Notation "A ::= B >*> N" := (assign (assign2 (rotR N)   (toLArg A) (toRArg B))) (at level 70).
Notation "A ::= B <<  N"  := (assign (assign2 (shiftL N) (toLArg A) (toRArg B))) (at level 70).
Notation "A ::= B >>  N" := (assign (assign2 (shiftR N) (toLArg A) (toRArg B))) (at level 70).
Notation "A ::=<< N "    := (assign (update1 (shiftL N) (toLArg A))) (at level 70).
Notation "A ::=>> N "    := (assign (update1 (shiftR N) (toLArg A))) (at level 70).
Notation "A ::=<*< N "    := (assign (update1 (rotL N)  (toLArg A))) (at level 70).
Notation "A ::=>*> N "    := (assign (update1 (rotR N)  (toLArg A))) (at level 70).

Notation "A ::== B"      := (assign (assign2 nop (toLArg A) (toRArg B))) (at level 70).
Notation "'MOVE'  B 'TO'   A [- N -]"       := (moveTo A (exist _ (N%nat) _) B) (at level 200, A ident).
(**

One another irritant in writing code is that the array indexing needs
proof that the bounds are not violated. We use the following tactic to
dispose off all such obligations.

*)


Tactic Notation "verse" uconstr(B) := (refine B; repeat match goal with
                                                       | [ |- _ mod _ < _ ] => apply NPeano.Nat.mod_upper_bound
                                                       | _                  => omega
                                                       end
                                     ).

(* begin hide *)
Require Import Verse.PrettyPrint.
Section PrettyPrintingInstruction.

  (** The variable type for our instructions *)
  Variable v : VariableT.


  (** The pretty printing instance for our variable *)
  Variable vPrint : forall k ty, PrettyPrint (v k ty).

  (** The pretty printing of our argument *)
  Fixpoint argdoc {aK}{k}(ty : type k ) (av : arg v aK k ty) :=
    match av with
    | var v       => doc v
    | const c     => doc c
    | index v (exist _ n _) => doc v <> bracket (decimal n)
    end.

  Global Instance arg_pretty_print : forall aK k ty, PrettyPrint (arg v aK k ty)
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
  Local Definition convertEndian e d :=
    match e with
    | bigE => text "bigEndian" <> paren d
    | littleE => text "littleEndian" <> paren d
    | _       => d
    end.

  (** The pretty printing of assignment statements **)
  Global Instance assignment_pretty_print : PrettyPrint (assignment v)
    := { doc := fun assgn =>  match assgn with
                              | assign3 o x y z => mkAssign o (doc x) (doc y) (doc z)
                              | update2 o x y   => mkUpdate o (doc x) (doc y)
                              | @assign2 _ ty u x y   =>
                                match u with
                                | bitComp  | nop  => mkAssign u (doc x) empty (doc y)
                                | shiftL n | shiftR n  => mkAssign u (doc x) (doc y) (decimal n)
                                | rotL n   | rotR n    => mkRot ty u (doc x)(doc y)
                                end
                              | @update1 _ ty u x      =>
                                let xdoc := doc x in
                                match u with
                                | bitComp  | nop       => mkAssign u xdoc empty xdoc
                                | shiftL n | shiftR n  => mkUpdate u xdoc (decimal n)
                                | rotL n   | rotR n    => mkRot ty u xdoc xdoc
                                end
                              end
       }.

  Global Instance instruction_pretty_print : PrettyPrint (instruction v)
    := { doc := fun i => match i with
                         | assign a => doc a
                         | @moveTo _ _ e _  a (exist _ i _) b
                           => doc a <_> bracket (doc i) <_> EQUALS <_> convertEndian e (doc b)
                         | destroy v => text "destroy" <_> doc v
                         end
       }.

End PrettyPrintingInstruction.

(* end hide *)


(** *** Illustrative example of the notation.

To demonstrate the use of this notation and its pretty printed form,
we first define an inductive type whose constructors are the variables
of our program.

*)

Module Demo.
  Inductive MyVar : VariableT :=
  |  X : MyVar direct Word8
  |  Y : MyVar direct Word64
  |  Z : MyVar direct (Vector128 Word32)
  |  A : MyVar memory (array 42 bigE Word8)
  .



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
  Import Vector.
  Import Vector.VectorNotations.
  Import Verse.Word.


  (**

For illustration consider the following (nonsensical) program
fragment.  Notice that we can directly use the variables (as in [X],
[Y], Z) or constants (the [Ox "..."] are appropriate constants) as
operands of the programming fragment.


   *)


  Definition vec_const : constant (Vector128 Word32) := [ Ox "12345678"; Ox "12345678"; Ox "12345678"; Ox "12345678"].

  Definition prog : block MyVar.
    verse [ X ::= X << 5 ;
            X ::=>> 5;
            X ::= X [+] (A[- 2 -]);
            X ::= X [+] Ox "55";
            Z ::= Z [+] vec_const
          ]%list.

  Defined.


  (** The above program fragment is pretty printable because the
      underlying variable type ([MyVar] in this case), is pretty printable
*)


  Compute layout (doc prog).
End Demo.
