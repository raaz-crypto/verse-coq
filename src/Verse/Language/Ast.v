(** printing power2m   $ 2^m     $ # 2<sup> m   </sup> # *)
(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)


(** * The abstract syntax tree of Verse.

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

Some correctness and safety properties for features like array
indexing has been built into the ast and thus gives a correct by
construction style of AST.


We begin by defining the types for the language.

 *)


(* begin hide *)
Require Import Verse.Language.Types.
Require        Verse.Target.C.Ast.

Import EqNotations.
(* end hide *)


(** * Operators of Verse language.

We define the arithmetic and bitwise operators that the verse language
supports. Target languages have support for these. The nat parameter
captures the arity of the operator. The shifts and rotate instructions
are arity one here because they only support constant
offsets. Cryptographic implementations only need this and infact it is
better to restrict to such shifts/rotates --- argument dependent
shifts and rotates can become side channel leaking instructions.

We define the verse language operators as C operators with the
additional rotation operation (for some inexplicable reasons C still
does not have rotation instructions in the standards).

 *)

Inductive op : nat -> Set :=
| cop     : forall n, C.Ast.op n -> op n
| rotL    : nat -> op 1
| rotR    : nat -> op 1
.

Arguments cop [n].

(** We now define the Verse version of the C operators *)
Definition plus     := cop Ast.plus.
Definition minus    := cop Ast.minus.
Definition mul      := cop Ast.mul.
Definition quot     := cop Ast.quot.
Definition rem      := cop Ast.rem.
Definition bitOr    := cop Ast.bitOr.
Definition bitAnd   := cop Ast.bitAnd.
Definition bitXor   := cop Ast.bitXor.
Definition bitComp  := cop Ast.bitComp.
Definition shiftL m := cop (Ast.shiftL m).
Definition shiftR m := cop (Ast.shiftR m).

(**
    The verse language ast is defined for a generic type system

*)
Section Code.

  Variable ts : typeSystem.

  Variable v : VariablesOf ts.
  Arguments v [k].


  (** Expressions that can occur on the left of an assignment. *)
  Inductive lexpr : typeOf ts Types.direct -> Set :=
  | var   :  forall {ty}, v ty -> lexpr ty
  | deref :  forall {ty b e}, v (arrayType ts b e ty)-> {i | i < b} -> lexpr ty.

  (** The expression type *)

  Inductive expr : typeOf ts Types.direct -> Type :=
  | cval     : forall {ty}, constOf ts ty -> expr ty
  | valueOf  : forall {ty}, lexpr ty -> expr ty
  | app      : forall {ty} {arity : nat}, op arity -> Vector.t (expr ty) arity -> expr ty
  .

  (** ** Instructions

   Verse supports C like assignments and update operations. Other than
   these common assignment, update, Verse support are two special
   instructions which deserve some mention.

   Firstly there is the [move] instruction that moves the value
   located in an variable into the lhs. While move ensures that the
   value that is currently in the variable on its rhs gets copied into
   the lhs, it gives no guarantee on the value currently in its
   rhs. Assignments on the other hand preserve the value of the
   rhs. This semantics of move enable it to sometimes compile down to
   more efficient instructions. For example, when moving a value from
   a variable [x] to an array index [a[- i -]], which is of an endian
   different from that of the machine, the move instruction needs to
   just endian switch [x], and copy where as an assignment has to
   endian switch [x], copy and then switch back.

   The [clobber] instruction is like a no-op but it invalidates the
   contents of a given variable. A move has the semantics of the
   corresponding assignment followed by a clobber on the rhs.  Note
   that the [clobber] and [move] need not erase the value in the
   rhs. So using clobber to erase a secret value is not safe.
   Typically clobber instructions will be ignored when generating
   instructions.

   *)

  Inductive instruction ty : Type :=
  | assign    : lexpr ty -> expr ty  -> instruction ty
  | update    : lexpr ty -> forall n, op (S n) -> Vector.t (expr ty)  n -> instruction ty
  | increment : lexpr ty -> instruction ty
  | decrement : lexpr ty -> instruction ty
  | moveTo    : lexpr ty -> v ty  -> instruction ty
  | clobber   : v ty -> instruction ty.


  Definition statement := sigT instruction.
  Definition code      := list statement.

End Code.

Arguments expr [ts].
Arguments lexpr [ts].
Arguments instruction [ts].
Arguments code [ts].
Arguments statement [ts].


(**

Many cryptographic primitives work on streams of data that are divided
into chunks of fixed size. The record [iterator] is essentially the
body of the an iterator that works with such a stream of blocks of
type [ty].

 *)
Record iterator ts (v : VariablesOf ts) (ty : typeOf ts memory)
  := { setup    : code v;
       process  : v memory ty -> code v;
       finalise : code v
     }.

Arguments iterator [ts].
Arguments setup [ts v ty].
Arguments process [ts v ty].
Arguments finalise [ts v ty].


Arguments var [ts v ty].
Arguments deref [ts v ty b e].
Arguments assign [ts v ty].
Arguments cval [ts v ty].
Arguments valueOf [ts v ty].
Arguments app [ts v ty arity].
Arguments clobber [ts v ty].
Arguments moveTo [ts v ty].
Arguments update [ts v ty] le [ n ].
Arguments increment [ts v ty].
Arguments decrement [ts v ty].
(** ** Ast under type level transations. *)

Section Translate.
  Variable src : typeSystem.
  Variable tgt : typeSystem.
  Variable tr  : typeTranslation src tgt.
  Variable v   : VariablesOf tgt.

  Section ForATypeTY.

    Definition translateLexpr ty (le : lexpr (transVar tr v) ty)
      : lexpr v (typeTrans tr ty).
      refine (match le with
              | @var _ _ ty x => var (ty := typeTrans tr ty) x
              | @deref _ _ ty b e a i => @deref tgt v (typeTrans tr ty) b e _ i
              end). rewrite <- (arrayCompatibility tr). exact a.
    Defined.

    Arguments translateLexpr [ty] _.

    Fixpoint translateExpr ty (e : expr (transVar tr v) ty)
      : expr v (typeTrans tr ty)
      := match e with
         | cval c      => cval (constTrans tr c)
         | valueOf x   => valueOf (translateLexpr x)
         | app op args => app op (Vector.map (translateExpr _) args)
         end.

    Definition translateInstruction ty (i : instruction (transVar tr v) ty)
      : instruction v (typeTrans tr ty) :=
      match i with
      | assign x e => assign (translateLexpr x) (translateExpr _ e)
      | update x o args => update (translateLexpr x) o (Vector.map (translateExpr _) args)
      | increment x => increment (translateLexpr x)
      | decrement x => decrement (translateLexpr x)
      | moveTo x y  => (fun yp : v direct (typeTrans tr ty) => moveTo (translateLexpr x) yp) y
      | clobber x   => (fun xp : v direct (typeTrans tr ty) => clobber xp) x
      end.

  End ForATypeTY.

  Definition translateStatement (s : statement (transVar tr v) )
    : statement v
    := match s with
       | existT _ ty i => existT _ _ (translateInstruction ty i)
       end.

  Definition translateCode : code (transVar tr v) -> code v
    := List.map translateStatement.

  Definition translateIterator memty (itr : iterator (transVar tr v) memty)
    : iterator v (typeTrans tr memty)
    := {| setup := translateCode (setup itr);
          finalise := translateCode (finalise itr);
          process  := fun x => translateCode (process itr x)
       |}.

End Translate.
Arguments translateLexpr [src tgt] _ [v ty].
Arguments translateExpr [src tgt] _ [v ty].
Arguments translateInstruction [src tgt] _ [v ty] _.
Arguments translateCode [src tgt] _ [v].
Arguments translateIterator [src tgt] _ [v].

Require Import Verse.Error.
Section Compile.

  Variable src : typeSystem.
  Variable tgt : typeSystem.
  Variable tr  : typeCompile src tgt.
  (*
  Section Recover.
    Variable func : forall ts : typeSystem, typeOf ts direct -> Type.
    Variable ty   : typeOf src direct.
    Definition extract (u : func (resultSystem tgt) (typeTrans tr ty)) :=
      :=
        match typeTrans tr ty as ty0
              return  match ty0 with
                      | {- good -} => func tgt good
                      | error _   => Empty_set + {TranslationError}
                      end
        with
          | {- good -}


    *)

  Variable v   : VariablesOf tgt.

  Section ForATypeTY.
    Variable ty  : typeOf src direct.

    Definition compileLexpAux ty0 : lexpr (resultVar v) ty0 ->
                                    match ty0 with
                                    | {- tyc -} => lexpr v tyc
                                    | error _   => Empty_set + {TranslationError}
                                    end
      := match ty0 with
         | {- good -} => fun l => match l with
                                  | @var _ _ {- good -}  x        => var x
                                  | @deref _ _ {- good -} _ _ a i => deref (ty:=good) a i
                                  end
         | error err  => fun l => error (CouldNotTranslateBecause l err)
         end.

    Definition compileLexp (l : lexpr (compileVar tr v) ty)
      := compileLexpAux _ (translateLexpr tr l).

    Fixpoint compileExpAux ty0 (e : expr (resultVar v) ty0)
      (* This definition does not compile without the return type *)
      : match ty0 with
        | {- tyc -} => expr v tyc
        | error _   => Empty_set + {TranslationError}
        end
      := match e with
         (* The match annotation is not required once return type is made explicit.
           Does not work with the match annotation but without the return type! *)
         | @cval _ _ {- good -} c        => @cval _ _ good c
         | @valueOf _ _ {- good -} x     => valueOf (compileLexpAux _ x)
         | @app _ _ {- good -} _ op args => app op (Vector.map (compileExpAux _) args)
         | @cval _ _ (error err) _       => error (CouldNotTranslateBecause e err)
         | @valueOf _ _ (error err) x    => error (CouldNotTranslateBecause e err)
         | @app _ _ (error err) _ _ _    => error (CouldNotTranslateBecause e err)
         end.

    Fixpoint compileExp (e : expr (compileVar tr v) ty)
      := compileExpAux _ (translateExpr tr e).

    Definition compileInstAux ty0 : instruction (resultVar v) ty0
                                    ->  match ty0 with
                                        | {- tyc -} => instruction v tyc
                                        | error _   => Empty_set + {TranslationError}
                                        end
      (* Type signature added above just for clarity *)
      := match ty0 return
               instruction (resultVar v) ty0
               ->  match ty0 with
                   | {- tyc -} => instruction v tyc
                   | error _   => Empty_set + {TranslationError}
                   end
         with
         | {- good -} => fun i => match i with
                                  | assign x e => assign (compileLexpAux _ x)
                                                         (compileExpAux _ e)
                                  | update x o args => update (compileLexpAux _ x)
                                                              o
                                                              (Vector.map (compileExpAux _) args)
                                  | increment x => increment (compileLexpAux _ x)
                                  | decrement x => decrement (compileLexpAux _ x)
                                  | moveTo x y  => moveTo (compileLexpAux _ x)
                                                          y
                                  | clobber x   => clobber x
                                  end
         | error err => fun i => error (CouldNotTranslateBecause i err)
         end.

    Definition compileInstruction ty (i : instruction (compileVar tr v) ty)
      := compileInstAux _ (translateInstruction tr i).


    Definition instructionErr (ty : typeOf (resultSystem tgt) direct)
      := match ty with
         | {- good -} => instruction v good
         | error _    => Empty_set + {TranslationError}
         end.


    Definition compileStatement (s : statement (compileVar tr v))
      :=
      match typeTrans tr (projT1 s) as ty0 return
            typeTrans tr (projT1 s) = ty0 -> statement v + {TranslationError}
      with
      | {- good -} => fun tyeq => {- existT _ good
                                            (rew [instructionErr] tyeq
                                              in
                                                (compileInstruction _ (projT2 s))) -}
      | error _    => fun _    => error (CouldNotTranslate s)
      end eq_refl.

    Definition compileCode (c : code (compileVar tr v))
      : code v + {TranslationError}
      :=
        let compile := fun s => liftErr (compileStatement s) in
        merge _ _ (List.map compile c).

  (* There is some yak shaving here as we essentially need to have a compile versions
       of the translation; I am not sure whether we can reuse the work done for translation
   *)
  End ForATypeTY.


End Compile.
(*

(** Compute the size of a type in bytes. *)
Fixpoint sizeOf {k} (ty : type k) :=
  match ty with
  | word n         => 2 ^ n
  | multiword m n  => 2 ^ m * 2 ^ n
  | array n _ tw => n * sizeOf tw
  end.


(** Often we need to existentially quantify over types and other
    objects. This definition is just for better readability.
 *)

Definition some {P: Type} (A : P -> Type) := sigT A.

*)

(*
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Error.

Require Import Bool.
Require Import Omega.
Require Import List.
Import ListNotations.

Generalizable All Variables.
Set Implicit Arguments.

(* end hide *)

(** * The Verse language as an inductive data type.

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

  Definition context := forall {k} {ty : type k}, v ty -> @typeDenote _ tyD _ ty.

  Definition ctxtP   := (context * context)%type.

  (*
     This particular design choice allows one to define a valid Prop even
     with a context that has some (unused) Invalid values.
     The simpler
                `pure_context -> Prop`
     would not allow one to extract a Prop with an impure context that has
     only unused Invalid values.
  *)

  Definition annotation := (ctxtP -> Prop).

  Inductive codeline : Type :=
  | assert : annotation  -> codeline
  | inst   : instruction -> codeline
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
    | assign e  =>
      match e with
      | assign2 nop _ _    => false
      | assign3 _ a1 a2 a3 => (isEndian nHostE a1) || (isEndian nHostE a2) || (isEndian nHostE a3)
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
Arguments context [_] _.
Arguments annotation [tyD] _.
Arguments codeline [tyD] _.
Arguments inst [tyD v] _.
Arguments code [tyD] _.

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

(* begin hide *)
Arguments iterator [tyD] _ _.
Arguments setup [tyD ty v] _.
Arguments process [tyD ty v] _ _.
Arguments finalise [tyD ty v] _.

Arguments var [v aK k ty] _ .
Arguments const [v ty] _ .
Arguments index [v aK  b e ty]  _ _.
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
*)