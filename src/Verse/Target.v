(* begin hide *)
Require Verse.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Ast.
Require Import Verse.Language.Types.
Require Import Verse.Error.
Require Import Verse.Target.C.Ast.

Require Verse.Scope.
Require Import Vector.
Import Vector.VectorNotations.
(* end hide *)

(** * Function signature.

The function signature captures three things about a function in the
target language. The ordered list of its parameters, the local
variables, and the allocated registers. These information is relevant
for generating the entry/exit code for the function (what registers
need saving etc) and the C prototype for the function.

*)
Record funSig ts (v : Variables.U ts) :=
  FunSig {
      nParameters : nat;
      nLocals     : nat;
      nRegisters  : nat;
      paramTypes  : Scope.type ts nParameters;
      localTypes  : Scope.type ts nLocals;
      registerTypes : Scope.type ts nRegisters;
      parameters : Scope.allocation v paramTypes;
      locals     : Scope.allocation v localTypes;
      registers  : Scope.allocation v registerTypes
    }.

Arguments FunSig [_ _ _ _ _ _ _ _].
(* begin hide *)

Arguments nParameters [ts v].
Arguments nLocals     [ts v].
Arguments nRegisters  [ts v].
Arguments paramTypes  [ts v].
Arguments localTypes  [ts v].
Arguments registerTypes [ts v].
Arguments parameters [ts v].
Arguments locals     [ts v].
Arguments registers  [ts v].

(* end hide *)



(** * The Target configuration module.

A target for verse needs to implement a module with the following
signature that abstracts out various target specific details of the
generator.

*)

Module Type CONFIG.


  (** The statements of the target language. *)
  Parameter statement : Type.

  Parameter programLine  : Type.

  (** The type system on the target side. *)
  Parameter typeS : TypeSystem.typeSystem.

  (** The conversion from verse types to the target type system. *)
  Parameter typeCompiler : TypeSystem.compiler verse_type_system typeS.

  (** The variables used on the target side. For actual machines these
   are often machine registers or indirections via machine registers
   *)
  Parameter variables    : Variables.U typeS.

  (** ** Two phase code generation.

     The compilation of verse code to the target languages happens in
     two phases. In the first stage, only a type transformation is
     done using the [typeCompiler]. The errors that are generated in
     this phase are only type checking errors, which occurs when we
     use a variable or a constant in verse that does not have its
     corresponding type in the target. One can see this phase as a
     type erasure from the richly typed verse language to the weakly
     typed target language. This phase is completely taken care of by
     the structural compilers available in [Code.compile] and
     [Iterator.compile] which makes use of the type compiler
     [typeCompiler]. So the nothing other than the [typeCompiler] is
     required to perform this phase.

     On successful completion of the first phase, we get the same
     structural code as the source but with the underlying type system
     being that of the target type system. We then need to convert
     this code into actual target specific instructions which is what
     the [compileCode] function does. This phase is target specific
     and needs to be defined in this config module. One can think of
     this as the instruction selection phase of the "compiler" and
     unsupported instructions lead to translation errors. To make this
     compilation phase predictable, a property that is critical in
     ensuring that hidden side channel leaks do not happen during
     compilation, it should be the case that verse code should more or
     less be translated verbatim and anything which is more
     complicated than the instruction set of the target should result
     in a translation error.

   *)

  Parameter compileCode   : code variables -> list statement + {TranslationError}.

  (** *** Compiling Iterators.

      Iterators process a stream of blocks each of which is
      transformed by the code available through the [process] field of
      the [iterator] record. On the target side we have a pointer
      variable that iterates over the blocks one at a time and
      transforming it using the [process] component. We needs some
      additional configuration to make this work out. Firstly, given
      an iterator that processes blocks each of which is of a given
      type [ty] in the verse world, we need to have a type [pty] in
      the target world that corresponds to pointers to the verse
      type. Note that this pointer type might not be representable in
      verse.

   *)

  Parameter pointerType  : forall (memty : Types.type memory) good,
      Types.compile typeCompiler memty = {- good -}
      -> typeOf typeS memory.

  (** We need a way to dereference the current block so that the
     [process] fragment of the iterator can work on it.

  *)
  Parameter dereference  : forall memty good (pf : Types.compile typeCompiler memty = {- good -}),
      variables memory (pointerType memty good pf) -> variables memory good.

  (** Finally, we need a way to iterate over all the blocks. This is
      used to compile the loop that uses the [process] field of the
      iterator to

   *)

  Parameter mapOverBlocks : forall mem ty,
      variables memory mem -> (**  Block pointer variable *)
      variables direct ty  -> (** Counter variable       *)
      list statement       -> (** Things to do on a single block *)
      list statement.

  Parameter makeFunction
    : forall name : Set,
      name
      -> funSig typeS variables
      -> list statement -> programLine.

End CONFIG.

(**
    This is the code generation module that takes as parameters a
    target configuration module and generates the actual function that
    corresponds to the verse code. There are two variants, code
    generator for straight line programs as well as code generator for
    iterators.
*)

Module CodeGen (T : CONFIG).

  Definition variables := T.variables.
  Arguments variables [k].
  (** The code generation function only needs three things to
      complete its code generation, the allocations (in the target
      variable) to hold the parameters, local variables, and the
      register variables for the function/iterator. Having got these
      three, it essentially just generates code by filling in these
      allocations and using the config module [T] to get the final
      target AST. The core is thus pretty simple but we need a lot of
      boilerplate to make the types work out.

      - We need to convert the allocation that we have (these are in
        terms of target variables) into that of the source variables
        so that they can be filled into our [scoped] source code. This
        is achieved by the function [toVerseAllocation].

      - The filled source code (the type system being that of the
        verse language) needs to be "typeChecked" and transformed into
        target type system. This is achieved by the function
        [typeCheckedTransform].

      - We then need to convert these type checked and transformed
        code into the target specific ast for which we make use of the
        functions from the config module T.

   *)

  Definition toVerseAllocation    := Scope.Allocation.coCompile T.typeCompiler.
  Definition typeCheckedTransform := Code.compile T.typeCompiler.

  (** To carry out these transformation, we also need compatibility of
      the allocation types which the following predicate asserts *)

  Definition compatible n st ss := Scope.Types.compatible (n:=n) T.typeCompiler st ss.

  (* begin hide *)
  Arguments toVerseAllocation [n st ss] _ [v].
  Arguments typeCheckedTransform [v].
  Arguments compatible [n].

  (* end hide *)

  (** The essential arguments for the code generator are the
      allocations to parameters, local variables, and register
      variables. However, to get to that point, we need a large number
      of auxiliary types and helper functions. We package all these
      into the following section.  *)

  Section Shenanigans.

    (** The set of possible names of the function. At the code
        generation stage the user can instantiate it with a particular
        set.  *)
    Variable name : Set.

    (** The name of the function for which the code is to be
        generated. *)
    Variable fname : name.

    (** The iterator function iterates over blocks and the type [memty]
        is the type of a single block. Straight line functions do no
        need this parameter.
    *)
    Variable memty       : typeOf verse_type_system memory.

    (** Now comes the scope type of parameter, locals, and register
       variables of the iterator/function.

     *)
    Variable p l r : nat.
    Variable pvs  : Scope.type verse_type_system p.
    Variable lvs  : Scope.type verse_type_system l.
    Variable rvs  : Scope.type verse_type_system r.

    (**
       The abstracted form of function/iterator is just a nested
       scoped straight line code/iterator

     *)

    Definition abstracted v CODE
      := Scope.scoped v pvs (
                        Scope.scoped v lvs (
                                       Scope.scoped v rvs CODE)).

    (** ** Allocating target variables.

        The variables of the verse program when translated to the
        target code needs allocations over target variables. We have
        allocations for parameters, locals, and register variables for
        the function and in addition for iterators we have two
        additional parameter, namely [blockPtrVar] and
        [counterVar]. The iterator is expected to be called by setting
        the [blockPtrVar] to point to the first block in the sequence
        and setting the [counterVar] to the number of blocks to be
        processed.

     *)

    Variable blockType       : typeOf T.typeS memory.
    Variable blockTypeCompat : Types.compile T.typeCompiler memty = {- blockType -}.

    Definition blockPtrType := T.pointerType memty blockType blockTypeCompat.
    Variable blockPtrVar : T.variables memory blockPtrType.

    Variable counterType    : typeOf T.typeS direct.
    Variable counterVar  : T.variables direct counterType.


    (** Both iterators and ordinary straight line functions now need
        their allocation for their parameters, local variables and
        registers. The next set of section variables build towards
        this. *)



    (**
        The allocation types for parameters, locals, and registers
        on the target side.
     *)
    Variable pts  : Scope.type T.typeS p.
    Variable lts  : Scope.type T.typeS l.
    Variable rts  : Scope.type T.typeS r.

    (**
       Proofs of compatibility of the allocation types on the verse
       and the target side.

     *)

    Variable pCompat : compatible pts pvs.
    Variable lCompat : compatible lts lvs.
    Variable rCompat : compatible rts rvs.


    (** Having captured all the above types we now get to the three
       relevant arguments to the code generator namely the allocation
       used to hold the parameters, locals and register variables on
       the target side.  *)

    Variable params : Scope.allocation T.variables pts.
    Variable locals : Scope.allocation T.variables lts.
    Variable regs   : Scope.allocation T.variables rts.


    (**
        Using the Variables.coCompile we can convert into variables on
        the verse type system.
     *)
    Definition verse_params := toVerseAllocation pCompat params.
    Definition verse_locals := toVerseAllocation lCompat locals.
    Definition verse_regs   := toVerseAllocation rCompat regs.

    (** We now give the code generator for the straight line functions
        which has as body an [abstracted] verse code block
     *)
    Definition function
               (func   : forall v, abstracted v (code v))
      : T.programLine + { TranslationError }
      := let body := Scope.fill verse_regs (Scope.fill verse_locals (Scope.fill verse_params (func _)))
         in btc <- typeCheckedTransform body ;
              btarget <- T.compileCode btc;
              let fsig := FunSig params locals regs
              in {- T.makeFunction name fname fsig btarget -}.



    (** Finally, there are two additional variables that we need on
        the target side which does not occur in the parameters, locals
        or registers --- the [blockPtrVar] which needs to be set by
        the caller to point to the starting block and the
        [counterVar], which needs to be set to the number of blocks
        that needs processing. Since these two variables are to be set
        by the caller, they become additional parameters to the
        iterator function.
     *)

    (**

        The [process] field in the iterator body is a function that
        takes a target variable that points to the current block. This
        target variable is in essence the dereference of the
        [blockPtrVar] and is captured by the definition below. the
        [process] field does not move [blockPtrVar] directly and only
        has access to the current block through this dereferenced
        [blockVar]

     *)

    Definition  blockVar := T.dereference memty blockType blockTypeCompat blockPtrVar.

    (** The full parameter declaration for the iterator. Note that we
        need to add two additional variables one for the block pointer
        and other for the counter
     *)

    Definition fullpts := existT _ _ blockPtrType :: existT _ _ counterType :: pts.

    (** Given an allocation for the parameters, this generates *)
    Definition fullParams : Scope.allocation T.variables fullpts
      := (blockPtrVar , (counterVar, params)).

    Definition iterativeFunction
               (iFunc       : forall v, abstracted v (iterator v memty))
      : T.programLine + {TranslationError}
      := let iter    := Scope.fill verse_regs
                                   (Scope.fill verse_locals
                                               (Scope.fill verse_params (iFunc _))) in
         iterComp <- Iterator.compile T.typeCompiler iter blockTypeCompat blockVar;
           let fsig := FunSig fullParams locals regs in
           pre  <- T.compileCode (Iterator.preamble iterComp);
             middle <- T.compileCode (Iterator.loopBody iterComp);
             post <- T.compileCode (Iterator.finalisation iterComp);
             let lp := T.mapOverBlocks _ _ blockPtrVar counterVar middle in
             {- T.makeFunction name fname fsig (pre ++ lp ++ post)%list -}.
  End Shenanigans.

  Arguments function [name] _
            [p l r].
  Arguments iterativeFunction [name] _ _ [p l r] pvs lvs rvs blockType blockTypeCompat
            blockPtrVar [counterType].

  Definition targetTypes {n} (vts : Scope.type Types.verse_type_system n)
    := pullOutVector (map pullOutSigT (Scope.Types.translate T.typeCompiler vts)).

  (** These notations are only for making our life easy when writing
      these functions with an incredibly many arguments. We do not
      really care about their use in pretty printing and hence they
      are marked as (only parsing). This also suppress some warnings
      from Coq *)

  Notation Function name pvsf lvsf rvsf
    := ( let pvs := Verse.infer pvsf in
         let lvs := Verse.infer lvsf in
         let rvs := Verse.infer rvsf in
         function name pvs lvs rvs
                  (recover (targetTypes pvs))
                  (recover (targetTypes lvs))
                  (recover (targetTypes rvs))
                  eq_refl eq_refl eq_refl
       )
         (only parsing).

  Notation Iterator name memty pvsf lvsf rvsf bPtrVar ctrVar
    := (
        let memtyTgt : typeOf T.typeS memory
            := recover (Types.compile T.typeCompiler memty) in
        let pvs := Verse.infer pvsf in
        let lvs := Verse.infer lvsf in
        let rvs := Verse.infer rvsf in
        let pvt : Scope.type T.typeS _ := recover (targetTypes pvs) in
        let lvt : Scope.type T.typeS _ := recover (targetTypes lvs) in
        let rvt : Scope.type T.typeS _ := recover (targetTypes rvs) in
        iterativeFunction name memty
                          pvs lvs rvs
                          memtyTgt eq_refl
                          bPtrVar ctrVar
                          pvt lvt rvt
                          eq_refl eq_refl eq_refl
       )
         (only parsing).

  Definition programLine := T.programLine.
End CodeGen.
