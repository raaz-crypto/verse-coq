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

Require Import Verse.TypeSystem.

Require Import Verse.Monoid.Interface.

Import EqNotations.
(* end hide *)

(**
    The verse language ast is defined for a generic type system

 *)

Section VerseCode.

  Variable ts : typeSystem.

  Variable v : Variables.U ts.
  Arguments v [k].

  (** Expressions that can occur on the left of an assignment. *)
  Inductive lexpr : typeOf ts TypeSystem.direct -> Type :=
  | var   :  forall {ty}, v ty -> lexpr ty
  | deref :  forall {ty b e}, v (arrayType ts b e ty)-> {i | i < b} -> lexpr ty.

  (** The expression type *)

  Inductive expr : typeOf ts TypeSystem.direct -> Type :=
  | cval     : forall {ty}, constOf ts ty -> expr ty
  | valueOf  : forall {ty}, lexpr ty -> expr ty
  | uniOp    : forall {ty}, operator ts ty 1 -> expr ty -> expr ty
  | binOp    : forall {ty}, operator ts ty 2 -> expr ty -> expr ty -> expr ty
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
  | assign      : lexpr ty -> expr ty  -> instruction ty
  | binopUpdate : lexpr ty -> operator ts ty 2 -> expr ty -> instruction ty
  | uniopUpdate : lexpr ty -> operator ts ty 1 -> instruction ty
  | moveTo    : lexpr ty -> v ty  -> instruction ty
  | clobber   : v ty -> instruction ty.


  Definition statement := sigT instruction.
  Definition code := list statement.

  Variable mline : Type.

  Inductive line `{Interface _ mline v} :=
  | instruct  : forall ty, instruction ty -> line
  | inline    : mline                     -> line
  .

  Definition lines `{Interface _ mline v} := list line.

End VerseCode.

Arguments expr [ts].
Arguments lexpr [ts].
Arguments instruction [ts].
Arguments instruct [ts v mline _ _ _ ty].
Arguments inline [ts v _ _ _ _].
Arguments code [ts].
Arguments statement [ts].
Arguments line [ts] _ _ [_ _ _].
Arguments lines [ts] _ _ [_ _ _].

(**

Many cryptographic primitives work on streams of data that are divided
into chunks of fixed size. The record [iterator] is essentially the
body of the an iterator that works with such a stream of blocks of
type [ty].

 *)
Record iterator ts (v : Variables.U ts) (ty : typeOf ts memory)
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
Arguments binOp [ts v ty].
Arguments uniOp [ts v ty].
Arguments clobber [ts v ty].
Arguments moveTo [ts v ty].
Arguments binopUpdate [ts v ty].
Arguments uniopUpdate [ts v ty].

(** ** Ast under type level transations. *)

Require Import Verse.Error.

Module LExpr.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt) (ty : typeOf src direct)
             (le : lexpr (Variables.Universe.coTranslate tr v) ty)
  : lexpr v (Types.translate tr ty)
    := match le with
       | @var _ _ ty x => var (ty := Types.translate tr ty) x
       | @deref _ _ ty b e a i =>
         let compatPf := arrayCompatibility tr b e ty in
         let ap  := Variables.translate tr a in
         deref (rew compatPf in ap) i
       end.

  Arguments translate [src tgt] tr [v ty].

  Definition result tgt (v : Variables.U tgt) (ty : Types.result tgt direct)
    := match ty with
       | {- good -} => lexpr v good
       | error _   => Empty_set + {TranslationError}
       end.

  Arguments result [tgt].

  Definition extract tgt (v : Variables.U tgt) ty :
    lexpr (Variables.Universe.inject v) ty -> result v ty
    := match ty with
       | {- good -} => fun l => match l with
                            | @var _ _ {- good -}  x        => var x
                            | @deref _ _ {- good -} _ _ a i => deref (ty:=good) a i
                            | _ => idProp
                            end
       | error err
         => fun l => error (CouldNotTranslateBecause l err)
       end.
  Arguments extract [tgt v ty].
(*
  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v  : Variables.U tgt)
             (ty : typeOf src direct)
             (le : lexpr (Variables.Universe.coCompile cr v) ty)
    : result v (Types.compile cr ty)
    := extract (translate cr le).

  Arguments compile [src tgt] cr [v ty].
*)
End LExpr.

Module Expr.

  Fixpoint translate {src tgt}
           (tr : TypeSystem.translator src tgt)
           {v       : Variables.U tgt}
           {ty}
           (e : expr (Variables.Universe.coTranslate tr v) ty)
  : expr v (Types.translate tr ty)
    := match e with
         | cval c        => cval (constTrans tr c)
         | valueOf x     => valueOf (LExpr.translate tr x)
         | uniOp o e0    => uniOp (opTrans tr o) (translate tr e0)
         | binOp o e0 e1 => binOp (opTrans tr o) (translate tr e0) (translate tr e1)
       end.


  Arguments translate [src tgt] tr [v ty].

  Definition result tgt
             (v : Variables.U tgt) (ty : Types.result tgt direct)
    := match ty with
       | {- good -} => expr v good
       | error _   => Empty_set + {TranslationError}
       end.
  Arguments result [tgt].


  Fixpoint extract {tgt}
           {v : Variables.U tgt}
           {ty} (e : expr (Variables.Universe.inject v) ty)
           : result v ty
    := match e in expr _ ty0 return result v ty0
       with
       | @cval _ _ {- good -} c        => @cval _ _ good c
       | @valueOf _ _ {- good -} x     => valueOf (LExpr.extract x)
       | @binOp _ _ {- good -} o e0 e1 => binOp (ty:=good) o (extract e0) (extract e1)
       | @uniOp _ _ {- good -} o e0    => uniOp (ty:=good) o (extract e0)
       | @cval _ _ (error err) _
       | @valueOf _ _ (error err) _
       | @binOp _ _ (error err) _ _ _
       | @uniOp _ _ (error err) _ _
         => error (CouldNotTranslateBecause e err)
       end.

  Arguments extract [tgt v ty].
  (*
  Fixpoint compile src tgt
           (cr : TypeSystem.compiler src tgt)
           (v  : Variables.U tgt)
           (ty : typeOf src direct)
           (e : expr (Variables.Universe.coCompile cr v) ty)
    := extract (translate cr e).
  Arguments compile [src tgt] cr [v ty].
   *)
End Expr.

Module Instruction.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
             ty (i : instruction (Variables.Universe.coTranslate tr v) ty)
  : instruction v (Types.translate tr ty) :=
    match i with
    | assign x e => assign (LExpr.translate tr x) (Expr.translate tr e)
    | binopUpdate x o e0 => binopUpdate (LExpr.translate tr x) (opTrans tr o) (Expr.translate tr e0)
    | uniopUpdate x o    => uniopUpdate (LExpr.translate tr x) (opTrans tr o)
    | moveTo x y  => (fun yp : v direct (Types.translate tr ty) => moveTo (LExpr.translate tr x) yp) y
    | clobber x   => (fun xp : v direct (Types.translate tr ty) => clobber xp) x
    end.

  Arguments translate [src tgt] tr [v ty].
  Definition result tgt
             (v  : Variables.U tgt)
             (ty : Types.result tgt direct)
    := match ty with
       | {- tyc -} => instruction v tyc
       | error _   => Empty_set + {TranslationError}
       end.

  Arguments result [tgt].

  Definition extract tgt
             (v : Variables.U tgt)
             (ty : Types.result tgt direct)
    : instruction (Variables.Universe.inject v) ty -> result v ty
    := match ty with
       | error err =>  fun i => error (CouldNotTranslateBecause i err)
       | {- good -} =>
           let lext := LExpr.extract (ty:={- good -}) in
           let ext  := Expr.extract (ty:={- good -}) in
           fun i =>
               match i with
               | assign x e => assign (lext x) (ext e)
               | binopUpdate x o e0 => binopUpdate (lext x) o (ext e0)
               | uniopUpdate x o  => uniopUpdate (lext x) o
               | moveTo x y  => moveTo (lext x) y
               | clobber x   => clobber x
               end

         end.

  Arguments extract [tgt v ty].

  Definition compile
             src tgt
             (cr : TypeSystem.compiler src tgt)
             (v : Variables.U tgt)
             ty (i : instruction (Variables.Universe.coCompile cr v) ty)
    := extract (translate cr i).

  Arguments compile [src tgt] cr [v ty].

End Instruction.

Module Statement.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
             (s : statement (Variables.Universe.coTranslate tr v))
  : statement v
  := match s with
     | existT _ ty i => existT _ _ (Instruction.translate tr i)
     end.

  Arguments translate [src tgt] tr [v].

  Definition result tgt (v : Variables.U tgt)
             := statement v + {TranslationError}.

  Arguments result [tgt].


  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v : Variables.U tgt)
             (s : statement (Variables.Universe.coCompile cr v))
             : result v
    := match Types.translate cr (projT1 s) as ty0
             return Types.translate cr (projT1 s) = ty0
                    -> result v
       with
       | {- good -}
         => fun tyeq => {- existT _ good
                                  (rew [Instruction.result _] tyeq
                                    in
                                      (Instruction.compile _ (projT2 s))) -}
       | error _
         => fun _ => error (CouldNotTranslate s)
       end eq_refl.

  Arguments compile [src tgt] cr [v].

End Statement.



Module Code.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
  : code (Variables.Universe.coTranslate tr v) -> code v
  := List.map (Statement.translate (v := v)tr).

  Arguments translate [src tgt] tr [v].

  Definition result tgt (v : Variables.U tgt) := code v + {TranslationError}.

  Arguments result [tgt].

  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v : Variables.U tgt)
             (c : code (Variables.Universe.coCompile cr v)) : result v
    :=  let compile := fun s => liftErr (Statement.compile cr s) in
        pullOutList (List.map compile c).
  Arguments compile [src tgt] cr [v].

End Code.


Module Iterator.

  (**
      The translation of an iterator is pretty straight forward and
      results in an iterator
   *)



  Definition translate src tgt
             (tr : translator src tgt)
             (v : Variables.U tgt)
             memty
             (itr : iterator (Variables.Universe.coTranslate tr v) memty)
  : iterator v (Types.translate tr memty)
    := {| setup    := Code.translate tr (setup itr);
          finalise := Code.translate tr (finalise itr);
          process := fun x => Code.translate tr (process itr x)
       |}.


  (**

      The result of a compilation cannot be an iterator due to the
      field process being a lambda form and the best we can do is v ->
      code v + Error. The following type captures compiles form of an
      iterator.

      Recall that the iterator is supposed to iterate over a set of
      blocks each of which needs to be processed by the
      loopBody. However, the code to step to the next block is /not/
      included in it as typically this would be target dependent and
      not expressible in the verse sub language itself.

   *)

  Record compiled tgt (v : Variables.U tgt) := { preamble : code v;
                                                 loopBody : code v;
                                                 finalisation : code v
                                               }.



  Arguments translate [src tgt] tr [v memty].

  Definition compile src tgt
             (cr : compiler src tgt)
             (v  : Variables.U tgt)
             memty
             (itr : iterator (Variables.Universe.coCompile cr v) memty)
             (good : typeOf tgt memory)
             (pf : Types.compile cr memty = {- good -})
             (x  : v memory good)
    : compiled tgt v + {TranslationError}
    := (stup <- Code.compile cr (setup itr);
        fnls <- Code.compile cr (finalise itr);
        prcs <- Code.compile cr (process itr (rew <- pf in Variables.inject x));
        inleft {| preamble := stup;  loopBody := prcs; finalisation := fnls |}).

  Arguments compile [src tgt] cr [v memty] itr [good].

  Arguments compiled [tgt].
  Arguments preamble [tgt v].
  Arguments loopBody [tgt v].
  Arguments finalisation [tgt v].
End Iterator.
