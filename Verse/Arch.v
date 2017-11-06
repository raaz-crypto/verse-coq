Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Types.Internal.
Require Import Verse.PrettyPrint.
Require Import Verse.Types.
Require Import Verse.Error.

Require Import String.
Require Import List.
Import ListNotations.
Require Import Ensembles.

Set Implicit Arguments.

(** * Architecture

An architecture is characterised by its

1. register set

2. the instruction set

An abstract assembly language program in this architecture uses both
registers and stack variables. We abstract such variables in the type
machine var. The architecture should provide a translation of the
instruction that use machine vars to actual machine code.


*)

Module Type ARCH.

  (** Name of the architecture family *)
  Parameter name     : string.

  (** The registers for this architecture *)
  Parameter register : varT.

  Parameter machineVar : varT.

  (** A way to embed register into the machine variable *)
  Parameter embedRegister : forall {ty : type}, register ty -> machineVar ty.

  (** Encode the architecture specific restrictions on the instruction set **)

  Parameter Word          : type.

  Parameter supportedInst : Ensemble (instruction machineVar).
  Parameter supportedType : Ensemble type.

  (**

      When generating code for a function, we need to know the following

      1. How much additional space on the stack is to be reserved for use
         by local variables.

      2. What registers should be saved by the function.

      3. Any other architecture specific information.

      The functionDescription gives these information.

   *)

  Parameter functionDescription : Type.

End ARCH.


(** * Frame management.

The next module abstracts the machine dependent frame management for
functions in verse.  A verse function supports only statements that
refer to the following types of variables.

1. The parameters

2. The local variables.

In particular, we do not have nested functions and hence all variables
mentioned in the function are within the current frame.

*)


Module Type FRAME(A : ARCH).


  (** The state of the frame as seen from the callee when it is
      entered. The type [frameState] captures the description of the
      function calling frame.  This includes information on the
      registers and stack locations used for the parameters or local
      variables.  The frame also has comes with a name, the name of
      the function.  It is this name that allows it to be called from
      a C program.

   *)

  Parameter frameState : Type.

  (** The expression [emptyFrame "foo"] creates an empty frame for a function named "foo" *)
  Parameter emptyFrame : string -> frameState.

  (** ** Parameter and local varaible allocation

  The next few function builds the function frame incrementally. We
  can add a parameter to the function, allocate a local variable or
  mark a register for use in the function.

  *)

  
  (** Add parameter to the function frame. *)
  Parameter addParam : frameState ->
                       forall ty, A.machineVar ty * frameState + { ~ A.supportedType ty }.

  (** Allocate a local varaible on the stack *)
  Parameter stackAlloc : frameState ->
                      forall ty, A.machineVar ty * frameState + { ~ A.supportedType ty }.

  (** Mark a register for use *)
  Parameter useRegister : frameState ->
                          forall ty (r : A.register ty), option frameState.


  
  (** Finally we generate the function description from the frame
      state. When creating the function description, we should call
      this at the end after all the stack, register and parameters
      have been fixed.
   *)
  Parameter description : frameState -> A.functionDescription.
 
  

End FRAME.

Module Type CODEGEN (A : ARCH).

  (** Emit the code for a single instruction for *)
  Parameter emit : forall (i : instruction (A.machineVar)), Doc + { not (A.supportedInst i) }.

  (** Instruction(s) to be added to the begining of the code given its
      frameState. These instructions typically allocated space on the
      stack and save caller set of registers (on th stack) *)
  Parameter prologue : A.functionDescription -> Doc.

  (** Restore the contents of the given register set. *)
  Parameter epilogue : A.functionDescription -> Doc.

  (** Bulk cryptographic primitives like ciphers, hashes, etc, require
      processing a sequence of blocks. This member function loops over
      a sequence of blocks of message type msgTy and runs the body on
      each of this block. It makes use of two machine variable. The
      first is a variable that (at the start of the loop) points to
      the start of the sequence and the second contains the number of
      blocks in the sequence.  This higher order function takes care
      of wrapping the body with an appropriate preamble and ensures
      incrementing the blockPtr appropriately.  *)
  Parameter loopWrapper : forall (blockType : type),
      A.machineVar (Ref blockType) -> (** The variable that points to the start of sequence *)
      A.machineVar A.Word          -> (** The number of elements of the block               *)
      Doc                          -> (** The body of the block                             *)
      Doc.

End CODEGEN.
