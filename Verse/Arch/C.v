Require Import Syntax.
Require Import Language.
Require Import Types.
Require Import Types.Internal.
Require Import Language.
Require Import Arch.
Require Import Function.
Require Import Word.
Require Import Error.
Require Import PrettyPrint.

Require Import List.
Require Import String.
Require Import Ensembles.
Require Import Program.Basics.


Module C <: ARCH.

  (** Name of the architecture family *)

  Definition name : string := "Portable-C".

  (** The registers for this architecture *)

  Inductive creg : varT :=
    cr (ty : type) : string -> creg ty.

  Inductive cvar : varT :=
  | inRegister (ty : type) : creg ty -> cvar ty
  | onStack    (ty : type) : string -> cvar ty
  .

  Definition register := creg.

  Definition machineVar := cvar.

  Definition embedRegister := inRegister.

  Definition supportedInst := Full_set (instruction machineVar).
  
  Inductive typesSupported : Ensemble type :=
  | uint8           : typesSupported Word8
  | uint16          : typesSupported Word16
  | uint32          : typesSupported Word32
  | uint64          : typesSupported Word64
  | carray {n e ty} : typesSupported ty -> typesSupported (array n e ty)
  .

  Definition supportedType := typesSupported.

  Record funAlloc (fv : FunVars) := fallocation
                                      {
                                        pa  : allocation machineVar (param fv);
                                        la : allocation machineVar (local fv);
                                      }.

  Definition frameDescription := { fv : FunVars & funAlloc fv }.

End C.

Module CFrame <: FRAME C.

  Import C.
  
  Definition frameState := C.frameDescription.

  Definition addParam (ty : type) (a : machineVar ty) (f : frameState) : frameState.
    refine (
  existT _ {| param := ty :: param (projT1 f); local := local (projT1 f) |} {| pa := _; la := _ |}
      ).
    simpl.
    exact ((a, pa _ (projT2 f))).
    exact (la _ (projT2 f)).
  Defined.

  Definition addLocal (ty : type) (a : machineVar ty) (f : frameState) : frameState.
    refine (
        existT _ {| param := param (projT1 f); local := ty :: local (projT1 f) |} {| pa := _; la := _ |}
      ).
    simpl.
    exact (pa _ (projT2 f)).
    exact ((a, la _ (projT2 f))).
  Defined.
  

  Definition paramAlloc (f : frameState) (ty : type) : frameState + { not (In _ supportedType ty) }.
    refine (
    let n := List.length (param (projT1 f)) in
    match ty with
    | word 0 
    | word 1 
    | word 2

    | word 3
    | array _ _ _ => inleft (addParam ty (onStack _ ("l_" ++ Internal.nat_to_str n)) f)
    | _           => inright _
    end
      ).
    all : unfold In;
      unfold supportedType;
      unfold not; intros; inversion H.
    Defined.

    Definition onStack (f : frameState) (ty : type) : frameState + { not (In _ supportedType ty) }.
      refine (
    let n := List.length (param (projT1 f)) in
    match ty with
    | word 0 
    | word 1 
    | word 2
    | word 3
    | array _ _ _ => inleft (addLocal ty (onStack _ ("l_" ++ Internal.nat_to_str n)) f)
    | _           => inright _
    end
        ).
      all : unfold In;
        unfold supportedType;
        unfold not; intro H; inversion H.
    Defined.
      
    Definition useRegister (ty : type) (f : frameState) (r : register ty) : frameState + { not (In _ supportedType ty) }.
      refine (
          let n := List.length (param (projT1 f)) in
          match ty with
          | word 0 
          | word 1 
          | word 2

          | word 3
          | array _ _ _ => inleft (addLocal ty (inRegister _ r) f)
          | _           => inright _
          end
        ).
      
      all : unfold In;
        unfold supportedType;
        unfold not; intro H; inversion H.
    Defined.

    Definition description : frameState -> frameDescription := id.

End CFrame.
