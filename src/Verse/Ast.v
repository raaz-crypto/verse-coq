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
Require Export Verse.Language.Repeat.

Import List.ListNotations.
Import EqNotations.
(* end hide *)

(**
    The verse language ast is defined for a generic type system

 *)

Section VerseCode.

  Variable ts : typeSystem.

  Variable v : Variables.U ts.

  (** Expressions that can occur on the left of an assignment. *)
  Inductive lexpr : {k & ts k} -> Type :=
  | var   :  forall {ty}, v (existT _ direct ty) -> lexpr (existT _ direct ty)
  | deref :  forall {ty b e}, v (existT _ _ (arrayType ts b e ty)) -> {i | i < b} -> lexpr (existT _ direct ty).

  (** The expression type *)

  Inductive expr : {k & ts k} -> Type :=
  | cval     : forall {ty}, constOf ts ty -> expr (existT _ direct ty)
  | valueOf  : forall {ty}, lexpr ty -> expr ty
  | uniOp    : forall {ty}, operator ts ty 1 -> expr (existT _ direct ty) -> expr (existT _ direct ty)
  | binOp    : forall {ty}, operator ts ty 2 -> expr (existT _ direct ty) -> expr (existT _ direct ty) -> expr (existT _ direct ty)
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

  Inductive instruction : {k & ts k} -> Type :=
  | assign      kty : lexpr kty -> expr kty  -> instruction kty
  | binopUpdate ty  : lexpr (existT _ direct ty) -> operator ts ty 2 -> expr (existT _ direct ty) -> instruction (existT _ direct ty)
  | uniopUpdate ty  : lexpr (existT _ direct ty) -> operator ts ty 1 -> instruction (existT _ direct ty)
  | moveTo      kty : lexpr kty -> v kty  -> instruction kty
  | clobber     kty : v kty -> instruction kty.

  Definition statement := sigT instruction.
  Definition code := list statement.

End VerseCode.

Arguments expr [ts].
Arguments lexpr [ts].
Arguments instruction [ts].
Arguments code [ts].
Arguments statement [ts].

(* We provide a coercion from `code` to `Repeat statement` so to still
   be able to use old code
*)
Coercion mapRep ts (v : Variables.U ts) (c : code v) : Repeat (statement v)
  := [repeat 1 c]%list.

(**

Many cryptographic primitives work on streams of data that are divided
into chunks of fixed size. The record [iterator] is essentially the
body of the an iterator that works with such a stream of blocks of
type [ty].

 *)
Record iterator ts (v : Variables.U ts) (ty : typeOf ts memory)
  := { setup    : Repeat (statement v);
       process  : v (existT _ _ ty) -> Repeat (statement v);
       finalise : Repeat (statement v)
     }.

Arguments iterator [ts].
Arguments setup [ts v ty].
Arguments process [ts v ty].
Arguments finalise [ts v ty].


Arguments var [ts v ty].
Arguments deref [ts v ty b e].
Arguments assign [ts v kty].
Arguments cval [ts v ty].
Arguments valueOf [ts v ty].
Arguments binOp [ts v ty].
Arguments uniOp [ts v ty].
Arguments clobber [ts v kty].
Arguments moveTo [ts v kty].
Arguments binopUpdate [ts v ty].
Arguments uniopUpdate [ts v ty].

(** ** Ast under type level transations. *)

Require Import Verse.Error.

Module LExpr.

  (** Function for renaming variables *)
  Definition rename {ts}{u v : Variables.U ts}(rn : Variables.renaming u v) {ty : some ts } (l : lexpr u ty)
  : lexpr v ty
    := match l with
       | var x     => var (rn _ x)
       | deref a i => deref (rn _ a) i
       end.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt) (ty : some (typeOf src))
             (le : lexpr (Variables.Universe.coTranslate tr v) ty)
  : lexpr v (Types.Some.translate tr ty)
    := match le in lexpr _ ty0 return lexpr _ (Types.Some.translate tr ty0)
       with
       | var x => var (ty := Types.translate tr _)
                      (Variables.translate tr x)
       | @deref _ _ ty b e a i =>
         let compatPf := arrayCompatibility tr b e ty in
         let ap  := Variables.translate tr a in
         deref (rew [fun t => v (existT tgt memory t)] compatPf in ap) i
       end.

  Arguments translate [src tgt] tr [v ty].

  Definition result tgt (v : Variables.U tgt) (ty : some (Types.result tgt))
    := match ty with
       | existT _ _ {- good -} => lexpr v (existT _ _ good)
       | existT _ _ (error _)  => Empty_set + {TranslationError}
       end.

  Arguments result [tgt].

  Definition extract tgt (v : Variables.U tgt) ty :
    lexpr (Variables.Universe.inject v) ty -> result v ty
    := match ty with
       | existT _ _ {- good -} => fun l => match l with
                            | @var _ _ {- good -}  x        => var (ty := good) x
                            | @deref _ _ {- good -} _ _ a i => deref (ty:=good) a i
                            | _ => idProp
                            end
       | existT _ _ (error err)
         => fun l => error (CouldNotTranslateBecause l err)
       end.
  Arguments extract [tgt v ty].

  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v  : Variables.U tgt)
             (ty : some (typeOf src))
             (le : lexpr (Variables.Universe.coCompile cr v) ty)
    : result v (Types.Some.compile cr ty)
    := extract (translate cr le).

  Arguments compile [src tgt] cr [v ty].


  (** ** Evaluation.
      An Lexpr over a typeDenote can be evaluated.
   *)
  Section Evaluation.
    Context {ts : typeSystem}{tyD : typeDenote ts}.

    Definition eval {T} (l : lexpr tyD T)
      : tyD _ (projT2 T)
    := match l in (lexpr _ s) return (tyD (projT1 s) (projT2 s)) with
       | var x => x
       | @deref _ _ ty b e v idx =>
           Vector.nth_order
             (rew [fun T0 : Type@{abstract_type_system.u0} => T0]
                  arrayCompatibility tyD b e ty
               in v)
             (proj2_sig idx)
       end.
  End Evaluation.
End LExpr.

Module Expr.

  (** Renaming variables in an expression *)
  Fixpoint rename {ts}{u v : Variables.U ts}(rn : Variables.renaming u v) {ty : some ts} (e : expr u ty)
  : expr v ty
    := match e with
         | cval c        => cval c
         | valueOf x     => valueOf (LExpr.rename rn x)
         | uniOp o e0    => uniOp o (rename rn e0)
         | binOp o e0 e1 => binOp o (rename rn e0) (rename rn e1)
       end.


  Fixpoint translate {src tgt}
           (tr : TypeSystem.translator src tgt)
           {v  : Variables.U tgt}
           {ty}
           (e : expr (Variables.Universe.coTranslate tr v) ty)
  : expr v (Types.Some.translate tr ty)
    := match e with
         | cval c        => cval (constTrans tr c)
         | valueOf x     => valueOf (LExpr.translate tr x)
         | uniOp o e0    => uniOp (opTrans tr o) (translate tr e0)
         | binOp o e0 e1 => binOp (opTrans tr o) (translate tr e0) (translate tr e1)
       end.


  Arguments translate [src tgt] tr [v ty].

  Definition result tgt
             (v : Variables.U tgt) (ty : some (Types.result tgt))
    := match ty with
       | existT _ _ {- good -} => expr v (existT _ _ good)
       | existT _ _ (error _)  => Empty_set + {TranslationError}
       end.
  Arguments result [tgt].


  Fixpoint extract {tgt}
           {v : Variables.U tgt}
           {ty} (e : expr (Variables.Universe.inject v) ty)
           : result v ty
    := match e in expr _ ty0 return result v ty0
       with
       | @cval _ _ {- good -} c        => @cval _ _ good c
       | @valueOf _ _ (existT _ _ {- good -}) x     => valueOf (LExpr.extract x)
       | @binOp _ _ {- good -} o e0 e1 => binOp (ty:=good) o (extract e0) (extract e1)
       | @uniOp _ _ {- good -} o e0    => uniOp (ty:=good) o (extract e0)
       | @cval _ _ (error err) _
       | @valueOf _ _ (existT _ _ (error err)) _
       | @binOp _ _ (error err) _ _ _
       | @uniOp _ _ (error err) _ _
         => error (CouldNotTranslateBecause e err)
       end.

  Arguments extract [tgt v ty].


  Definition compile src tgt
           (cr : TypeSystem.compiler src tgt)
           (v  : Variables.U tgt)
           (ty : some (typeOf src))
           (e : expr (Variables.Universe.coCompile cr v) ty)
    := extract (translate cr e).
  Arguments compile [src tgt] cr [v ty].


  (** ** Evaluation.
      An expression over a typeDenote can be evaluated.
   *)
  Section Evaluation.
    Context {ts : typeSystem}{tyD : typeDenote ts}.

    Fixpoint eval {T} (e : expr tyD T)
      :  tyD _ (projT2 T)
      := match e with
         | Ast.cval c => constTrans tyD c
         | Ast.valueOf lv => LExpr.eval lv
         | Ast.binOp o e0 e1 => (opTrans tyD o) (eval e0) (eval e1)
         | Ast.uniOp o e0    => (opTrans tyD o) (eval e0)
         end.

  End Evaluation.

End Expr.

Module Instruction.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
             ty (i : instruction (Variables.Universe.coTranslate tr v) ty)
  : instruction v (Types.Some.translate tr ty) :=
    match i with
    | assign x e => assign (LExpr.translate tr x) (Expr.translate tr e)
    | binopUpdate x o e0 => binopUpdate (LExpr.translate tr x) (opTrans tr o) (Expr.translate tr e0)
    | uniopUpdate x o    => uniopUpdate (LExpr.translate tr x) (opTrans tr o)
    | @moveTo _ _ kty x y  => (fun yp : v (Types.Some.translate tr kty) => moveTo (LExpr.translate tr x) yp) y
    | @clobber _ _ kty x   => (fun xp : v (Types.Some.translate tr kty) => clobber xp) x
    end.

  Arguments translate [src tgt] tr [v ty].
  Definition result tgt
             (v  : Variables.U tgt)
             (ty : some (Types.result tgt))
    := match ty with
       | existT _ _ {- tyc -} => instruction v (existT _ _ tyc)
       | existT _ _ (error _) => Empty_set + {TranslationError}
       end.

  Arguments result [tgt].

  Definition extract tgt
             (v : Variables.U tgt)
             (ty : {k & Types.result tgt k})
    : instruction (Variables.Universe.inject v) ty -> result v ty
    := match ty with
       | existT _ _ (error err) =>  fun i => error (CouldNotTranslateBecause i err)
       | existT _ _ {- good -} as ty0 =>
           fun i : instruction _ ty0 =>
             (* TODO : Surely the following match can be written better *)
             match i in instruction _ ty0
             with
               | @assign _ _ (existT _ _ {-g-}) x e => assign (LExpr.extract x) (Expr.extract e)
               | @binopUpdate _ _ {-g-} x o e0 => binopUpdate (LExpr.extract x) o (Expr.extract e0)
               | @uniopUpdate _ _ {-g-} x o  => uniopUpdate (LExpr.extract x) o
               | @moveTo _ _ (existT _ _ {-g-}) x y  => moveTo (LExpr.extract x) y
               | @clobber _ _ (existT _ _ {-g-}) x   => clobber (kty := existT _ _ g) x
               | _ => idProp
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
    := match Types.Some.translate cr (projT1 s) as ty0
             return Types.Some.translate cr (projT1 s) = ty0
                    -> result v
       with
       | existT _ _ {- good -}
         => fun tyeq => {- existT _ (existT _ _ good)
                                  (rew [Instruction.result _] tyeq
                                    in
                                      (Instruction.compile _ (projT2 s))) -}
       | existT _ _ (error _)
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

Module RepStatement.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
    : repeated (code (Variables.Universe.coTranslate tr v)) -> repeated (code v)
    :=  (push (Code.translate (v := v)tr)).

  Arguments translate [src tgt] tr [v].

  Definition result tgt (v : Variables.U tgt)
    := repeated (code v) + {TranslationError}.

  Arguments result [tgt].

  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v : Variables.U tgt)
             (c : repeated (code (Variables.Universe.coCompile cr v))) : result v
    := pullOutRep (push (Code.compile cr (v := v)) c).

  Arguments compile [src tgt] cr [v].

End RepStatement.

Module RepCode.

  Definition translate src tgt
             (tr : TypeSystem.translator src tgt)
             (v : Variables.U tgt)
  : Repeat (statement (Variables.Universe.coTranslate tr v)) -> Repeat (statement v)
  := List.map (RepStatement.translate tr (v := v)).

  Arguments translate [src tgt] tr [v].

  Definition result tgt (v : Variables.U tgt) := Repeat (statement v) + {TranslationError}.

  Arguments result [tgt].

  Definition compile src tgt
             (cr : TypeSystem.compiler src tgt)
             (v : Variables.U tgt)
             (c : Repeat (statement (Variables.Universe.coCompile cr v))) : result v
    :=  let compile := fun s => (List.map (RepStatement.compile cr (v := v)) s) in
        pullOutList (compile c).

  Arguments compile [src tgt] cr [v].

End RepCode.

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
    := {| setup    := RepCode.translate tr (setup itr);
          finalise := RepCode.translate tr (finalise itr);
          process := fun x => RepCode.translate tr (process itr x)
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

  Record compiled tgt (v : Variables.U tgt) := { preamble : Repeat (statement v);
                                                 loopBody : Repeat (statement v);
                                                 finalisation : Repeat (statement v)
                                               }.



  Arguments translate [src tgt] tr [v memty].

  Definition compile src tgt
             (cr : compiler src tgt)
             (v  : Variables.U tgt)
             memty
             (itr : iterator (Variables.Universe.coCompile cr v) memty)
             (good : typeOf tgt memory)
             (pf : Types.compile cr memty = {- good -})
             (x  : v (existT _ _ good))
    : compiled tgt v + {TranslationError}
    := do stup <- RepCode.compile cr (setup itr) ;;
       do fnls <- RepCode.compile cr (finalise itr) ;;
       do prcs <- RepCode.compile cr (process itr (rew <- f_equal _ pf in Variables.inject x)) ;;
        pure {| preamble := stup;  loopBody := prcs; finalisation := fnls |}.

  Arguments compile [src tgt] cr [v memty] itr [good].

  Arguments compiled [tgt].
  Arguments preamble [tgt v].
  Arguments loopBody [tgt v].
  Arguments finalisation [tgt v].
End Iterator.
