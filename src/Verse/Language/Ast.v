(* begin hide *)
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Error.

Require Import Bool.
Require Import Omega.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

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

Section AST.

  Variable tyD : typeC TypeDenote.

  Variable v   : VariableT.


  (** Type that captures a memory variable's indices. *)
  Definition Indices {b e ty} (_ : v (array b e ty)) := { i : nat | i < b }.


  (** ** Arguments.

      Each verse program fragment consists of instructions applied to
      some arguments. Variables are one form of arguments, but so does
      indexed arrays or constants.

   *)

  Inductive argKind := lval | rval.
  Inductive arg : argKind -> VariableT :=
  | var   : forall aK, forall {k} {ty : type k}, v ty -> arg aK ty
  | const : forall {ty : type direct}, constant ty  -> arg rval ty
  | index : forall aK, forall {b : nat}{e : endian}{ty : type direct} (x : v (array b e ty)),
        Indices x  -> arg aK ty
  .

  Definition larg := arg lval.
  Definition rarg := arg rval.

  (** ** Assignment statement.

      One of the most important class of statement is the assignment
      statement. The following inductive type captures assignment statement.

   *)
  Inductive assignment : Type :=
  | extassign4
    : forall (ty : type direct), op binary ternary -> larg ty -> larg ty -> rarg ty -> rarg ty -> rarg ty -> assignment
  | extassign3
    : forall (ty : type direct), op binary binary -> larg ty -> larg ty -> rarg ty -> rarg ty -> assignment
  | assign3
    : forall (ty : type direct), binop -> larg ty -> rarg ty -> rarg ty -> assignment
  (** e.g. x = y + z *)
  | assign2
    : forall (ty : type direct), uniop -> larg ty -> rarg ty -> assignment (** e.g. x = ~ y   *)
  | update2
    : forall (ty : type direct), binop -> larg ty -> rarg ty -> assignment (** e.g. x += y    *)
  | update1
    : forall (ty : type direct), uniop -> larg ty -> assignment                   (** e.g. x ~= x    *)
  .

(**

Finally we have instructions that forms the basic unit of a program. A
program block is merely a list of instructions.

*)
  Inductive instruction : Type :=
  | assign    : assignment -> instruction
  | increment : forall (ty : type direct), larg ty -> instruction
  | decrement : forall (ty : type direct), larg ty -> instruction
  | moveTo    : forall b e ty, forall (x : v (array b e ty)), Indices x -> v ty -> instruction
  | clobber   : forall k (ty : type k), v ty -> instruction
  .

  Definition instructions := list instruction.

  Inductive contextErr := Invalid.
  Definition context := forall {k} {ty : type k}, v ty -> @typeDenote _ tyD _ ty + {contextErr}.

  Inductive annotation : Type :=
  | assert : (context -> Prop + {contextErr}) -> annotation
  | claim  : (context -> Prop + {contextErr}) -> annotation
  .

  Inductive codeline : Type :=
  | annot : annotation  -> codeline
  | inst  : instruction -> codeline
  .

  Global Definition code := list codeline.
  (* begin hide *)

  (* Some instruction error checking code *)

  Definition isEndian {aK} {k} {ty : type k} (nHostE : endian) (a : arg aK ty) :=
    let eqEndb (e f : endian) : bool :=
        match e, f with
        | littleE, littleE
        | bigE, bigE       => true
        | _, _             => false
        end
    in
    match a  with
    | @index  _ _ ne _ _ _ => eqEndb ne nHostE
    | _                 => false
    end.

  (** Function to check if a non-mov/store instruction uses arrays of offending endianness.
      Passing hostE as parameter allows all arrays. **)

  Definition endianError (nHostE : endian) (i : instruction) :=
    match i with
    | assign e  => match e with
                   | assign2 nop _ _    => false
                   | assign3 _ a1 a2 a3 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3)
                   | extassign4 _ a1 a2 a3 a4 a5 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3) || (isEndian nHostE a4) || (isEndian nHostE a5)
                   | extassign3 _ a1 a2 a3 a4 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3) || (isEndian nHostE a4)
                   | assign2 _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update2 _ a1 a2    => (isEndian nHostE a1) || (isEndian nHostE a2)
                   | update1 _ a1       => (isEndian nHostE a1)
                   end
    | _ => false
    end
  .

  Definition supportedInst (nhostE : endian) := fun i => endianError nhostE i = false.

  Definition instCheck e i : {supportedInst e i} + {~ supportedInst e i}
      := bool_dec (endianError e i) false.

  (* end hide *)


End AST.

Arguments Indices [v b e ty] _.
Arguments annotation [tyD] _.
Arguments codeline [tyD] _.
Arguments inst [tyD v] _.
Arguments code [tyD] _.

(* A macro to define an instruction block while being oblivious to
   semantic relevant details *)

Definition Code := let _ := mkTypeDenote StandardWord.wordDenote
  in @code _.

Section ASTFinal.

  Variable t  : kind -> Type.
  Variable tC : typeC (fun k : kind => t k + {UnsupportedType}).

  Variable constT : t direct -> Type.

  (* We abandon index safety at the machine level *)

  Class argC (a : GenVariableT t -> GenVariableT t) :=
    { mkVar : forall v k (ty : t k), v k ty -> a v k ty;
      mkConst : forall v (ty : t direct), constT ty -> a v direct ty;
      mkIndex : forall v (b : nat) (e : endian) (ty : t direct)
                (p : noErr (mkArray b e {- ty -})), v memory (getT p)
                -> nat -> a v direct ty
    }.

  (** An alternate way would be to write -

        Variable v : GenVariableT t.

        Class argC (a : GenVariableT t) := ...

      This would then allow, for example, an architecture to allow
      arrays to be pointed to by only some of it's registers.
  *)

  Variable vT : GenVariableT t.
  Variable aT  : GenVariableT t -> GenVariableT t.

  (* Since the instruction type for an architecture will be defined
     specifically for it's machineVar, instT is just a plain type
  *)

  Class instructionC (instT : Type) :=
    { UnsupportedInstruction : Prop;
      mkIncrement : forall ty : t direct, aT vT ty ->
                                          instT + {UnsupportedInstruction};
      mkDecrement : forall ty : t direct, aT vT ty ->
                                          instT + {UnsupportedInstruction};
      mkUpdate1 : forall ty : t direct, uniop ->
                                        aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkUpdate2 : forall ty : t direct, binop ->
                                        aT vT ty -> aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkAssign2 : forall ty : t direct, uniop ->
                                        aT vT ty -> aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkAssign3 : forall ty : t direct, binop ->
                                        aT vT ty -> aT vT ty -> aT vT ty ->
                                        instT + {UnsupportedInstruction};
      mkExtassign3 : forall ty : t direct, exop binary ->
                                           aT vT ty -> aT vT ty -> aT vT ty -> aT vT ty ->
                                           instT + {UnsupportedInstruction};
      mkExtassign4 : forall ty : t direct, exop ternary ->
                                           aT vT ty -> aT vT ty -> aT vT ty -> aT vT ty -> aT vT ty ->
                                           instT + {UnsupportedInstruction};
      mkMoveTo : forall b e ty (p : noErr (mkArray b e {- ty -})), vT (getT p) -> nat -> vT ty ->
                                                                   instT + {UnsupportedInstruction};
      mkNOP : instT (* A NOP instruction for CLOBBER translate.
                       This could, in a string translate, simply be
                       the empty string
                     *)
    }.

End ASTFinal.

Arguments instructionC [t _] _ _ _.
(* The following implicit argument declarations seem to be necessary to
   use the constructs without arguments. This is inspite of all arguments
   being implicit, albeit not maximally inserted, even prior to these
   declarations
*)
Arguments UnsupportedInstruction [t tC vT aT instT instructionC].
Arguments mkIncrement {t tC vT aT instT instructionC ty} _.
Arguments mkDecrement {t tC vT aT instT instructionC ty} _.
Arguments mkNOP [t tC vT aT instT instructionC].

(**

Many cryptographic primitives work on streams of data that are divided
into chunks of fixed size. The record [iterator] is essentially the
body of the an iterator that works with such a stream of blocks of
type [ty].

*)
Record iterator (tyD : typeC TypeDenote) (ty : type memory)(v : VariableT)
  := { setup    : code v;
       process  : v memory ty -> code v;
       finalise : code v
     }.

(* Semantic oblivious macro for iterators *)
Definition Iterator :=
  let _ := mkTypeDenote StandardWord.wordDenote
  in iterator _.

(* begin hide *)
Arguments iterator [tyD] _ _.
Arguments setup [tyD ty v] _.
Arguments process [tyD ty v] _ _.
Arguments finalise [tyD ty v] _.

Arguments var [v aK k ty] _ .
Arguments const [v ty] _ .
Arguments index [v aK  b e ty]  _ _.
Arguments extassign3 [v ty] _ _ _ _ _.
Arguments extassign4 [v ty] _ _ _ _ _ _.
Arguments assign3 [v ty] _ _ _ _ .
Arguments assign2 [v ty] _ _ _ .
Arguments update2 [v ty] _ _ _ .
Arguments update1 [v ty] _ _ .
Arguments assign [v] _ .
Arguments increment [v ty] _.
Arguments decrement [v ty] _.
Arguments moveTo [v  b e ty] _ _ _.
Arguments clobber [v k ty ] _.
(* end hide *)
