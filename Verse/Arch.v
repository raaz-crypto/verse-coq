Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Function.
Require Import Verse.Types.Internal.
Require Import String.
Require Import List.
Import ListNotations.
Require Import Ensembles.

Module Type ARCH.

  (** Name of the architecture family *)

  Parameter name     : string.

  (** The registers for this architecture *)

  Parameter register : varT.


  Definition var     := machineVar register.


  (** Encode the architecture specific restrictions on the instruction set **)

  Parameter supportedInst : Ensemble (instruction var).
  Parameter supportedTy   : Ensemble type.

  (*

  Not need as of now.

  Fixpoint wfinstrB (b : block var) : Prop :=
    match b with
    | [] => True
    | i :: bt => and (wfinstr i) (wfinstrB bt)
    end.
   *)

  (** Generate code with assurance of well formedness **)

  Parameter callConv : forall (paramTypes localTypes : listIn supportedTy),
      allocation var (proj_l paramTypes ++ proj_l localTypes).

  (*

  Parameter generate : forall b : block var, wftypesB b -> wfvarB b -> wfinstrB b -> string.

   *)
  (**

    Translate the assignment statement to assembly. Certain assignment
    instructions can fail, for example a three address assignment like
    [A <= B + C] is not supported on a 2-address machine like x86. and
    hence the result of a translation is a [option (list mnemonic)]
    instead of just a [list mnemonics].

   *)

  (** Convert the loop statement in assembly instruction. *)
  (*Parameter loop
  : forall {b : bound}{ty : type (Bounded b)},
      var reg ty -> arg reg ty -> list mnemonic -> list mnemonic.*)

End ARCH.

Module ArchAux (A : ARCH).

  Import A.

  (* Allocate with loopvar being allocated in a register by user *)
  Definition allocate loopvar
             (p          : In _ supportedTy loopvar)
             (paramTypes : listIn supportedTy)
             (localVars  : listIn supportedTy)
             (localReg   : listIn supportedTy)
             (f      : func loopvar (proj_l paramTypes) (proj_l localVars) (proj_l localReg))
             (lalloc : allocation var (loopvar :: (proj_l localReg)))
  : Function A.var loopvar * FAllocation var (proj_l paramTypes) (proj_l localVars) (proj_l localReg) loopvar :=

    let calloc            := callConv paramTypes localVars in
    let (palloc, lvalloc) := alloc_split var (proj_l paramTypes) (proj_l localVars) calloc in
    let lv                := fst (fst (alloc_split var (loopvar :: nil) (proj_l localReg) lalloc)) in
    let lralloc           := snd (alloc_split var (loopvar :: nil) (proj_l localReg) lalloc) in
    let f'                := fill var lralloc (fill var lvalloc (fill var palloc (f var))) in
    let fa                := {|
          pa      := palloc;
          lva     := lvalloc;
          lv      := lv;
          rva     := lralloc;
        |}
    in   
    pair f' fa.

  (* Allocate with loopvar being allocated on stack by callConv *)

                                
  Definition allocate' loopvar
             (p          : In _ supportedTy loopvar)
             (paramTypes : listIn supportedTy)
             (localVars  : listIn supportedTy)
             (localReg   : listIn supportedTy)
             (f      : func loopvar (proj_l paramTypes) (proj_l localVars) (proj_l localReg))
             (lalloc : allocation var (proj_l localReg))
    : Function var loopvar * FAllocation var (proj_l paramTypes) (proj_l localVars) (proj_l localReg) loopvar :=

    let p3'               := (exist _ loopvar p) :: localVars in
    let calloc            := callConv paramTypes ((exist _ loopvar p) :: localVars) in
    let (palloc, ra)      := alloc_split var (proj_l paramTypes) (loopvar :: (proj_l localVars)) calloc in
    let (lva,lvalloc)     := alloc_split var (loopvar :: nil) (proj_l localVars) ra in
    let lv                := fst lva in
    let f'                := fill var lalloc (fill var lvalloc (fill var palloc (f var))) in
    let fa                := {|
          pa      := palloc;
          lva     := lvalloc;
          lv      := lv;
          rva     := lalloc;
        |}
    in   
    pair f' fa.

End ArchAux.  
