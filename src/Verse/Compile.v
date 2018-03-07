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
| UnsupportedInstruction : forall {v : VariableT}, instruction v  -> CompileError
| UnsupportedType        : forall {k : kind}, type k -> CompileError
| UnavailableRegister    : forall {reg : VariableT}{k : kind}{ty : type k}, reg k ty -> CompileError.

(**

Compilation is parameterised by the architecture, the frame
management associated with the architecture and the code generator.

*)
Module Compiler (A : ARCH) (F : FRAME A) (C : CODEGEN A).

  (* Internal module to hide local variables *)
  Module Internal.


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
        C.sequenceInstructions <$> merge (List.map emitter insts).


    End CompileInstructions.

    Section CompileAllocations.

      Variable singleAlloc   :
        F.frameState ->
        forall k (ty : type k), A.machineVar ty * F.frameState + { ~ A.supportedType ty}.

      Definition Allocation l := allocation A.machineVar l * F.frameState + { CompileError }.

      Let liftTypeError
          {X : Type}
          {k : kind}
          {ty : type k}
          (action : X + { ~ A.supportedType ty}) : X + { CompileError }
        := match action  with
           | {- x -} => {- x -}
           | error _ => error (UnsupportedType ty)
           end.

      Fixpoint generate (s0 : F.frameState)(l : list (some type)) : Allocation l :=
        match l with
        | []           => {- (emptyAllocation A.machineVar, s0) -}
        | (existT _ _ ty :: rest)
          => a1 <- liftTypeError (singleAlloc s0 ty);
               let (v, s1) := a1
               in a2 <- generate s1 rest;
                    let (vs,s2) := a2
                    in {- ((v,vs), s2) -}
        end.

      Definition iterateFrame name ty := liftTypeError (F.iterateFrame name ty).
    End CompileAllocations.

    (** Generate a frame with the given set of parameters or die trying *)
    Definition params := generate F.addParam.

    (** Generate a frame with the given set of stack varaibles or die trying *)
    Definition stacks := generate F.stackAlloc.


    Fixpoint registers {l} : F.frameState ->
                             allocation A.register l -> Allocation l  :=
      match l with
      | []          => fun s0 _  => {- (emptyAllocation A.machineVar, s0) -}
      | (existT _ k ty :: tys)
        => fun s0 (rs : allocation A.register (existT _ k ty :: tys)) =>
             let (r,rest) := rs in
             match F.useRegister s0 r with
             | Some s1 => restAlloc <- registers s1 rest;
                            let (a,finalState) := restAlloc
                            in {- ((A.embedRegister r, a), finalState) -}
             | None    => error (UnavailableRegister r)
             end

      end.

    Section Function.
      Variable BODY : VariableT -> Type.
      Variable startState : F.frameState.

      (** Its parameters and stack variables *)
      Variable parameterTypes stackTypes : list (some type).

      Variable registerTypes : list (some type).

      (** Its register variables *)
      Variable registerVariables : allocation A.register registerTypes.


      Let BodyType v := scoped v parameterTypes
                               (scoped v stackTypes
                                       (scoped v registerTypes (BODY v))
                               ).


      Definition fillVars (functionBody : forall v, BodyType v) :=
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


    Let wrap descr (code : Doc + {CompileError}) := C.makeFunction descr <$> code.



    Definition compile name pts lts rts regs f
      := let state := F.emptyFrame name
         in result <- fillVars code state pts lts rts regs f;
              let (descr, code) := result  in wrap descr (compileInstructions code).

    Definition compileIterator ty name pts lts rts regs iterF
      := S <- iterateFrame name ty;
           let (iterVars, state) := S in
           let (codeV, countV)  := iterVars
           in result <- @fillVars (iterator ty) state pts lts rts regs iterF;
                let (descr, iF) := result in
                let setupCode       := compileInstructions (setup iF) in
                let iterationCode   := compileInstructions (process iF codeV) in
                let finaliseCode    := compileInstructions (finalise iF) in
                let body            := s <- setupCode; i <-  iterationCode; f <- finaliseCode;
                                         {- vcat [s; C.loopWrapper codeV countV i; f] -} in
                wrap descr body.

    Arguments compile _ _ _ [rts] _ _.
    Arguments compileIterator _ _ _ _ [rts] _ _.

  End Internal.

  Import Internal.
  Ltac function s p l r := simple refine (@compile s _ _ _ _ _);
                           [> declare p |  declare l | declare r | idtac | idtac ].
  Ltac iterator i s p l r := simple refine (@compileIterator i s _ _ _ _ _);
                              [> declare p |  declare l | declare r | idtac | idtac ].

End Compiler.
