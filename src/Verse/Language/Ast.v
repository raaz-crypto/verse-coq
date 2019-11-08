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
Require Import Verse.TypeSystem.
Require        Verse.Variables.

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
Section VerseCode.

  Variable ts : typeSystem.

  Variable v : Variables.U ts.
  Arguments v [k].


  (** Expressions that can occur on the left of an assignment. *)
  Inductive lexpr : typeOf ts TypeSystem.direct -> Set :=
  | var   :  forall {ty}, v ty -> lexpr ty
  | deref :  forall {ty b e}, v (arrayType ts b e ty)-> {i | i < b} -> lexpr ty.

  (** The expression type *)

  Inductive expr : typeOf ts TypeSystem.direct -> Type :=
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

End VerseCode.

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
Arguments app [ts v ty arity].
Arguments clobber [ts v ty].
Arguments moveTo [ts v ty].
Arguments update [ts v ty] le [ n ].
Arguments increment [ts v ty].
Arguments decrement [ts v ty].
(** ** Ast under type level transations. *)

Require Import Verse.Error.

Module LExpr.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt) ty
             (le : lexpr (Variables.translate tr v) ty)
  : lexpr v (Types.translate tr ty).
    refine (match le with
            | @var _ _ ty x => var (ty := Types.translate tr ty) x
            | @deref _ _ ty b e a i => @deref tgt v (Types.translate tr ty) b e _ i
            end). rewrite <- (arrayCompatibility tr). exact a.
    Defined.

  Arguments translate [src tgt] tr [v ty].

  Definition result tgt (v : Variables.U tgt) (ty : Types.result tgt direct)
    := match ty with
       | {- good -} => lexpr v good
       | error _   => Empty_set + {TranslationError}
       end.

  Arguments result [tgt].

  Definition extract tgt (v : Variables.U tgt) ty :
    lexpr (Variables.result v) ty -> result v ty
    := match ty with
       | {- good -} => fun l => match l with
                                | @var _ _ {- good -}  x        => var x
                                | @deref _ _ {- good -} _ _ a i => deref (ty:=good) a i
                                end
       | error err  => fun l => error (CouldNotTranslateBecause l err)
       end.
  Arguments extract [tgt v ty].

  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v  : Variables.U tgt)
             (ty : typeOf src direct)
             (le : lexpr (Variables.compile cr v) ty)
    : result v (Types.compile cr ty)
    := extract (translate cr le).

  Arguments compile [src tgt] cr [v ty].

End LExpr.

Module Expr.

  Fixpoint translate src tgt
           (tr : TypeSystem.translator src tgt)
           (v       : Variables.U tgt)
           ty
           (e : expr (Variables.translate tr v) ty)
  : expr v (Types.translate tr ty)
    := match e with
         | cval c      => cval (constTrans tr c)
         | valueOf x   => valueOf (LExpr.translate tr x)
         | app op args =>
           let argsT := Vector.map (translate _ _ _ _ _) args
           in app op argsT
         end.


  Arguments translate [src tgt] tr [v ty].

  Definition result tgt
             (v : Variables.U tgt) (ty : Types.result tgt direct)
    := match ty with
       | {- good -} => expr v good
       | error _   => Empty_set + {TranslationError}
       end.
  Arguments result [tgt].


  Fixpoint extract tgt
           (v : Variables.U tgt)
           ty (e : expr (Variables.result v) ty)
    : result v ty
    := match e with
       (* The match annotation is not required once return type is made explicit.
          D   oes not work with the match annotation but without the return type! *)
       | @cval _ _ {- good -} c        => @cval _ _ good c
       | @valueOf _ _ {- good -} x     => valueOf (LExpr.extract x)
       | @app _ _ {- good -} _ op args => app op (Vector.map (extract _ _ _) args)
       | @cval _ _ (error err) _       => error (CouldNotTranslateBecause e err)
       | @valueOf _ _ (error err) x    => error (CouldNotTranslateBecause e err)
       | @app _ _ (error err) _ _ _    => error (CouldNotTranslateBecause e err)
       end.
  Arguments extract [tgt v ty].
  Fixpoint compile src tgt
           (cr : TypeSystem.compiler src tgt)
           (v  : Variables.U tgt)
           (ty : typeOf src direct)
           (e : expr (Variables.compile cr v) ty)
    := extract (translate cr e).
  Arguments compile [src tgt] cr [v ty].
End Expr.

Module Instruction.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
             ty (i : instruction (Variables.translate tr v) ty)
  : instruction v (Types.translate tr ty) :=
    match i with
    | assign x e => assign (LExpr.translate tr x) (Expr.translate tr e)
    | update x o args =>
      let argsT := Vector.map (Expr.translate tr (v:=v)(ty:=ty)) args in
      update (LExpr.translate tr x) o argsT
    | increment x => increment (LExpr.translate tr x)
    | decrement x => decrement (LExpr.translate tr x)
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

    : instruction (Variables.result v) ty -> result v ty
      (* Type signature added above just for clarity *)
    := match ty
         with
         | {- good -}
           => fun i =>
                match i with
                | assign x e
                  => assign (LExpr.extract  x) (Expr.extract e)
                | update x o args
                  => let argsT := Vector.map (Expr.extract (tgt := tgt)(v:=v) (ty:={-good-})) args
                     in update (LExpr.extract x) o argsT
                | increment x => increment (LExpr.extract x)
                | decrement x => decrement (LExpr.extract x)
                | moveTo x y  => moveTo (LExpr.extract x) y
                | clobber x   => clobber x
                end
         | error err =>  fun i => error (CouldNotTranslateBecause i err)
         end.

  Arguments extract [tgt v ty].
  Definition compile
             src tgt
             (cr : TypeSystem.compiler src tgt)
             (v : Variables.U tgt)
             ty (i : instruction (Variables.compile cr v) ty)
    := extract (translate cr i).

  Arguments compile [src tgt] cr [v ty].
End Instruction.

Module Statement.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
             (s : statement (Variables.translate tr v))
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
             (s : statement (Variables.compile cr v))
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
  : code (Variables.translate tr v) -> code v
  := List.map (Statement.translate (v := v)tr).

  Arguments translate [src tgt] tr [v].

  Definition result tgt (v : Variables.U tgt) := code v + {TranslationError}.

  Arguments result [tgt].
  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v : Variables.U tgt)
             (c : code (Variables.compile cr v)) : result v
    :=  let compile := fun s => liftErr (Statement.compile cr s) in
        merge _ _ (List.map compile c).

End Code.

Module Iterator.

  Definition translate src tgt
             (tr : translator src tgt)
             (v  : Variables.U tgt)
             memty (itr : iterator (Variables.translate tr v) memty)
  : iterator v (Types.translate tr memty)
    := {| setup := Code.translate tr (setup itr);
          finalise := Code.translate tr (finalise itr);
          process  := fun x => Code.translate tr (process itr x)
       |}.

  Arguments translate [src tgt] tr [v memty].

  Definition result tgt (v : Variables.U tgt)
             (memty : Types.result tgt memory)
    := match memty with
       | {- good -} => iterator v good + {TranslationError}
       | _          => Empty_set + {TranslationError}
       end.

End Iterator.
