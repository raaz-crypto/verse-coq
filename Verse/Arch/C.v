(** * Architecture for Portable C-code

 *)

Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Arch.
Require Import List.
Require Import String.

Import ListNotations.

Module CArch : ARCH.

  Definition name : string:= "portable-C".

  Definition register (t : type) : Type := string.

  Definition supportedType (t : type) : Prop :=
    t = Word8 \/ t = Word16 \/ t = Word32 \/ t = Word64.

  Definition supports (i : instruction (machineVar register)) : Prop :=
    match i with
    | assign _ ainst => supportedType (Assignment.argtype ainst)
    end.

  Open Scope allocation_scope.
  Open Scope list_scope.

  Fixpoint allOnStack (n : nat)(l : list type) : allocation (machineVar register) l :=
    match l with
    | nil     => []
    | t :: ts => (onStack n :: allOnStack (S n) ts)%allocation
    end.

  Definition callConv (ptypes ltypes : list type) := allOnStack 0 (ptypes ++ ltypes).

End CArch.
