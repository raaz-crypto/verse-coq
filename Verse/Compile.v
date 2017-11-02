Require Import Arch.
Require Import Error.
Require Import PrettyPrint.
Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

(** * Compilation.

This module exposes code to compile verse programs to machine code. We
begin by defining the errors that can arise when code fragments are
compiled.

 *)

Inductive CompileError : Prop :=
| UnsupportedInstruction : forall {v : varT}, instruction v  -> CompileError
| UnsupportedType        : type -> CompileError
| UnavailableRegister    : forall {reg : varT}{ty : type}, reg ty -> CompileError.

(**

Compilation is parameterised by the architecture, the frame
management associated with the architecture and the code generator.

*)
Module Compiler (A : ARCH) (F : FRAME A) (C : CODEGEN A).

  (** First we given a function to compile a list of instructions *)
  Section CompileInstructions.

    Let liftInstructionError
        {X : Type}
        {i : instruction  A.machineVar}
        (action : X  + { ~ A.supportedInst i } ) : X + { CompileError }
      := match action with
         | {- x -} => {- x -}
         | error _ => error (UnsupportedInstruction i)
         end.


    Definition compileInstructions insts :=
    let emitter := fun i => liftInstructionError (C.emit i) in
    vcat <$> merge (List.map emitter insts).

  End CompileInstructions.


  Section CompileAllocations.

    Variable singleAlloc   :
      F.frameState ->
      forall ty : type, A.machineVar ty * F.frameState + { ~ A.supportedType ty}.

    Definition Allocation l := allocation A.machineVar l * F.frameState + { CompileError }.

    Let liftTypeError
        {X : Type}
        {ty : type}
        (action : X + { ~ A.supportedType ty}) : X + { CompileError }
      := match action  with
         | {- x -} => {- x -}
         | error _ => error (UnsupportedType ty)
         end.

    Fixpoint generate (s0 : F.frameState)(l : list type) : Allocation l :=
      match l with
      | []           => {- (emptyAllocation A.machineVar, s0) -}
      | (ty :: rest)
        => a1 <- liftTypeError (singleAlloc s0 ty);
             let (v, s1) := a1
             in a2 <- generate s1 rest;
                  let (vs,s2) := a2
                  in {- ((v,vs), s2) -}
      end.

  End CompileAllocations.

  (** Generate a frame with the given set of parameters or die trying *)
  Definition params := generate F.addParam.

  (** Generate a frame with the given set of stack varaibles or die trying *)
  Definition stacks := generate F.stackAlloc.


  Fixpoint registers {l} : F.frameState ->
    allocation A.register l -> Allocation l  :=
    match l with
            | []          => fun s0 _  => {- (emptyAllocation A.machineVar, s0) -}
            | (ty :: tys)
              => fun s0 (rs : allocation A.register (ty :: tys)) =>
                   let (r,rest) := rs in
                   match F.useRegister s0 r with
                   | Some s1 => restAlloc <- registers s1 rest;
                                let (a,finalState) := restAlloc
                                in {- ((A.embedRegister r, a), finalState) -}
                   | None    => error (UnavailableRegister r)
                   end

            end.

  Section Function.

    Variable B : varT -> Type.
    (** The name of the function *)
    Variable name : string.
    (** Its parameters and stack variables *)
    Variable parameterTypes stackTypes : list type.

    Variable registerTypes : list type.

    (** Its register variables *)
    Variable registerVariables : allocation A.register registerTypes.


    Let BodyType v := scoped v parameterTypes
                               (scoped v stackTypes
                                       (scoped v registerTypes (B v))
                               ).

    Let startState := F.emptyFrame name.

    Definition genCompile (functionBody : forall v, BodyType v) :=
      pA <- params startState parameterTypes;
        let (pVars, paramState) := pA in
        lA <- stacks paramState stackTypes;
          let (sVars, stackState) := lA in
          rA <- registers stackState registerVariables;
            let (rVars, finalState) := rA in
            let code := fill rVars
                             (fill sVars
                                   (fill pVars (functionBody A.machineVar))
                             ) in
            {- (F.description finalState, code) -}.



  End Function.

  Arguments genCompile _ _ _ _ [registerTypes] _ _.


  Definition compile name pts lts rts regs f
    :=
    result <-  @genCompile block name pts lts rts regs  f;
    let (descr, code) := result  in
    delimit (C.prologue descr)  (C.epilogue descr) <$> compileInstructions code.


  Arguments compile _ _ _ [rts] _ _.

End Compiler.
