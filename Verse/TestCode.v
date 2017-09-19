Require Import Verse.Arch.C.
Require Import Verse.Function.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.PrettyPrint.
Require Import Verse.Word.
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
            (* Try out all operators *)
            setup   := [
                        num <= tmp <+> Ox "abcd";
                         (* num <= tmp <-> num ; *) (* FIXME: Notation does not work *)
                          num      <= tmp      <*> arr[-1-] ;
                          num      <= arr[-1-] </> tmp ;
                          arr[-1-] <= tmp      <|> num ;
                          num      <= tmp      <&> arr[-1-];
                          num      <= tmp      <^> num ;

                          (* binary update *)
                          num <=+ tmp;
                          num <=- arr[-1-];
                          num <=* Ox "1234";
                          num <=/ tmp;
                          num <=| tmp;
                          num <=& tmp;
                          num <=^ tmp;

                          (* Unary operators *)
                          num      <=~ tmp;
                          tmp      <=  arr[-1-] <<  42;
                          tmp      <=  arr[-1-] >>  42;
                          num      <=  tmp     <*< 42;
                          arr[-1-] <=  tmp     >*> 42;

                          (* Unary update operators *)
                          tmp      <=<<  (42%nat);
                          tmp      <=>>  (42%nat);
                          num      <=<*< (42%nat);
                          arr[-1-] <=>*> (42%nat)
                       ]%list;
            loop    := fun lv : v loopvar => [num <=  tmp <+> arr[-1-] ];
            cleanup := []
          |}.

Definition lalloc : allocation CArch.var rv := (inRegister (cr Word16 "tmp"), (inRegister (cr Word32 "double"), tt)).

Definition code : Doc :=
  let '(f, fa) := allocate' Byte p paramTypes localVars localReg test lalloc in
  CArch.generate f fa.

Compute (layout code).
