Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Function.
Require Import Verse.Types.Internal.
Require Import Verse.PrettyPrint.
Require Import String.
Require Import List.
Import ListNotations.
Require Import Ensembles.

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

  Parameter supportedInst : Ensemble (instruction machineVar).
  Parameter supportedType : Ensemble type.

  (**

      The frame module (see below) incrementally builds a function
      frame. While generating code we need to know the description of
      the function, so that approprate prologue and epilogue can be
      appended on to the user code. This type captures that
      abstraction.

   *)

  Parameter frameDescription.


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

Inductive FrameError : Prop := RegisterInUse.

Module Type FRAME(A : ARCH).

  (**

  We incrementally build the frame description of the function. The
  [frameState] captures the description of the function calling frame.
  This includes information on the registers and stack locations used
  for the parameters or local variables.


  *)

  Parameter frameState : Type.

  (** The state of the frame as seen from the callee when it is
      entered.  At the point of entering, the stack frame only
      consists of the parameter to the function and hence this is
      parmeterised by the parameters of the function. Subsequent
      functions allocate more stuff from the frame.

      The frame also has comes with a name, the name of the function.
      It is this name that allows it to be called from a C program.

   *)

  Parameter enteringState : string -> list { ty : type | A.supportedType ty } -> frameState.

  Parameter onStack : frameState -> {ty : type | A.supportedType ty } -> frameState.

  Parameter useRegister : forall ty : type, frameState
                                            -> A.register ty -> frameState + {FrameError}.



  Parameter description : frameState -> A.frameDescription

End FRAME.


Print not.
Module Type CODEGEN (A : ARCH).

  (** Emit the code for a single instruction for *)
  Parameter emit : forall (i : instruction (A.machineVar)), Doc + { not (A.supportedInst i) }.

  (** Instruction(s) the save a given set of registers (on th stack) *)
  Parameter prologue : A.frameDescription -> Doc.

  (** Restore the contents of the given register set. *)
  Parameter epilogue : A.frameDescription -> Doc.

End CODEGEN.
