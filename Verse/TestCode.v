Require Import Verse.Arch.C.
Require Import Verse.Function.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.PrettyPrint.
Import Verse.Arch.C.CArchAux.

Require Import String.
Require Import List.
Import ListNotations.

Definition loopvar := Byte.
Definition pl      := [Word16].
Definition lv      := [ArrayT 3 hostE Word16].
Definition rv      := [Word16; Word32].

Ltac genPredList l :=
  let l' := match l with
            | nil => l
            | _ :: _ => l
            | _ => eval unfold l in l
  end
  in
  match l' with
  | nil        => exact nil
  | ?ty :: ?lt => refine (_ :: _); [ > refine (exist _ ty _); unfold Ensembles.In; repeat constructor | genPredList lt ]
  end.


Definition paramTypes : list {ty : type | Ensembles.In _ CArch.supportedTy ty}.
  genPredList pl.
Defined.

Definition localVars : list {ty : type | Ensembles.In _ CArch.supportedTy ty}.
  genPredList lv.
Defined.

Definition localReg : list {ty : type | Ensembles.In _ CArch.supportedTy ty}.
  genPredList rv.
Defined.

Definition p : Ensembles.In _ CArch.supportedTy loopvar.
  unfold Ensembles.In; repeat constructor.
Defined.

Definition test : func loopvar pl lv rv :=
  fun v : varT =>
    fun num : v Word16 =>
      fun arr : v (ArrayT 3 hostE Word16) =>
        fun (tmp : v Word16) (double : v Word32) =>
          {|
            name    := "test";
            setup   := [ num <= tmp <*> arr[-0-] ];
            loop    := fun lv : v loopvar => [num <=  tmp <+> arr[-1-] ];
            cleanup := []
          |}.

Definition lalloc : allocation CArch.var rv := (inRegister (cr Word16 "tmp"), (inRegister (cr Word32 "double"), tt)).

Definition code : Doc :=
  let '(f, fa) := allocate' Byte p paramTypes localVars localReg test lalloc in
  CArch.generate f fa.

Compute (layout code).
