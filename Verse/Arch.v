Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Function.
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

      The frame module (see below) incrementally builds a function
      frame. While generating code we need to know the description of
      the function, so that approprate prologue and epilogue can be
      appended on to the user code. This type captures that
      abstraction.

   *)

  Parameter frameDescription : Type.

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

  (**

  We incrementally build the frame description of the function. The
  [frameState] captures the description of the function calling frame.
  This includes information on the registers and stack locations used
  for the parameters or local variables.


  *)

  Inductive FrameError : Prop :=
  | RegisterInUse (ty : type) : A.register ty -> FrameError.

  Parameter frameState : Type.

  (** The state of the frame as seen from the callee when it is
      entered.  At the point of entering, the stack frame only
      consists of the parameter to the function and hence this is
      parmeterised by the parameters of the function. Subsequent
      functions allocate more stuff from the frame.

      The frame also has comes with a name, the name of the function.
      It is this name that allows it to be called from a C program.

   *)

  Parameter emptyFrame : forall s : string, frameState.
  
  Parameter paramAlloc : forall (f : frameState) (ty : type), (A.machineVar ty) * frameState + { ~ A.supportedType ty }.
                                                       
  Parameter onStack : forall (f : frameState) (ty : type), (A.machineVar ty) * frameState + { ~ A.supportedType ty }.

  Parameter useRegister : forall (ty : type) (fr : frameState) (r : A.register ty), (A.machineVar ty) * frameState + { ~ A.supportedType ty \/ FrameError }.

  Parameter description : frameState -> A.frameDescription.

End FRAME.

Module Type CODEGEN (A : ARCH).

  (** Emit the code for a single instruction for *)
  Parameter emit : forall (i : instruction (A.machineVar)), Doc + { not (A.supportedInst i) }.

  (** Instruction(s) the save a given set of registers (on th stack) *)
  Parameter prologue : A.frameDescription -> Doc.

  (** Restore the contents of the given register set. *)
  Parameter epilogue : A.frameDescription -> Doc.

  Parameter loopWrapper : forall (msgTy : type), A.machineVar msgTy -> A.machineVar A.Word -> Doc -> Doc.

End CODEGEN.

Module FUNWRITE (A : ARCH) (F : FRAME A) (C : CODEGEN A).

  Definition TyListError (l : list type) := exists ty : type, List.In ty l /\ ~ A.supportedType ty.
  Definition localAlloc (f : F.frameState) (ty : type) (ua : userTy A.register ty) : A.machineVar ty * F.frameState + { ~ A.supportedType ty \/ F.FrameError } :=
    match ua with
    | inR _ _ r => F.useRegister f r
    | onS _ ty  => match F.onStack f ty with
                   | inleft x => inleft x
                   | inright e => inright (or_introl e)
                   end
    end.
  
  Fixpoint pAlloc (p : list type) : forall (fr : F.frameState), F.frameState * allocation A.machineVar p + { TyListError p }.
    refine (
    fun (fr : F.frameState) => 
        match p with
        | [] => inleft (fr, emptyAllocation A.machineVar)
        | ty :: pt => match F.paramAlloc fr ty with
                      | inleft (vty, fr') => match pAlloc pt fr' with
                                             | inleft (fr'', a) => inleft (fr'', (vty, a))
                                             | inright _        => inright _
                                             end
                      | inright _         => inright _
                      end
        end
      ).
    unfold TyListError. unfold TyListError in t.
    inversion t.
    inversion H.
    refine (ex_intro _ x _ ).
    constructor.
    apply in_cons. all: trivial.

    unfold TyListError.
    refine (ex_intro _ ty _).
    constructor. apply in_eq. trivial.
  Defined.

  Fixpoint lAlloc (l : list type) : forall (la : userAlloc A.register l) (fr : F.frameState), F.frameState * allocation A.machineVar l + {TyListError l \/ F.FrameError}.
    refine (
          match l with
          | []       => fun _ (fr : F.frameState) =>
                          inleft (fr, emptyAllocation A.machineVar)
          | ty :: lt => fun (la : userAlloc A.register (ty ::lt)) (fr : F.frameState) =>
                          match localAlloc fr (fst la) with
                          | inleft (vty, fr') => match lAlloc lt (snd la) fr' with
                                                 | inleft (fr'', a) => inleft (fr'', (vty, a))
                                                 | inright _        => inright _
                                                 end
                          | inright _         => inright _
                          end
          end
      ).
    inversion o.
    refine (or_introl _ _).
    unfold TyListError in H. unfold TyListError.
    inversion H.
    inversion H0.
    refine (ex_intro _ x _).
    constructor.
    apply in_cons. all: trivial.
    exact (or_intror _ H).

    unfold TyListError.
    inversion o.
    refine (or_introl _ (ex_intro _ ty _)).
    constructor. apply in_eq. trivial.
    exact (or_intror _ H).
  Defined.

  Arguments lAlloc [l].

  Definition FunVarError (fv : FunVars) := TyListError (param fv) \/ TyListError (local fv).

  Definition fFill (fv : FunVars) (f : func A.register fv) : F.frameState * Function A.machineVar + { FunVarError fv \/ F.FrameError }.
    refine (
        let ef := F.emptyFrame (fname fv) in
        match pAlloc (param fv) ef with
        | inleft (fr, pa) => match lAlloc (snd f) fr with
                             | inleft (fr', la) => inleft (fr', fill la (fill pa (fst f A.machineVar)))
                             | inright _        => inright _
                             end
        | inright _       => inright _
        end
    ).
    inversion o.
    refine (or_introl _ (or_intror _ H)).
    refine (or_intror _ H).
    refine (or_introl _ (or_introl _ t)).
  Defined.

  Inductive FunError : Prop :=
  | InstructionNotSupported : instruction A.machineVar -> FunError
  | NoLoopVariable          : FunError
  | TypeNotSupported        : type -> FunError.

  Fixpoint blockWrite (b : block A.machineVar) : Doc + { FunError } :=
        nest 4 <$>
        match b with
        | []      => inleft empty
        | i :: bt => match C.emit i with
                     | inleft d => match blockWrite bt with
                                   | inleft ld => inleft (d <> ld)
                                   | inright e => inright e
                                   end
                     | inright _ => inright (InstructionNotSupported i)
                     end
        end.

  Definition gen (fv : FunVars) (f : func A.register fv) : Doc + { FunError }.
    refine (
        match param fv with
        | [] => inright NoLoopVariable
        | _  =>
          let fv' := {| param := A.Word :: param fv; local := local fv |} in
          let f'  : func A.register fv' :=
              ((fun v => @merge_scope _ [A.Word] _ _ (fun (n : v A.Word) => fst f v)), snd f) in
          match fFill f' with
          | inleft (fr, fn) => let fd := F.description fr in
                               C.prologue fd <> blockWrite (setup fn) <> C.loopWrapper 
          | inright _ => _
          end
        end
      ).
  
End FUNWRITE.