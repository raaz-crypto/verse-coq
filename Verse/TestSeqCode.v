Require Import Verse.Error.
Require Import Verse.Arch.C.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.PrettyPrint.
Require Import Verse.Word.
Require Import Verse.SeqFunction.

Require Import String.
Require Import List.
Import ListNotations.

Section TestFunction.

  Variable variable : varT.
  (* The parameters of the function *)
  Variable num : variable Word16.
  (* The local variables *)
  Variable arr      : variable (ArrayT 3 hostE Word16).
  (* The temp register *)
  Variable tmp       : variable Word16.
  Variable double    : variable Word32.

Definition test : ScopedSeqFunc Byte variable :=
  {|
    (* Try out all operators *)
    prologue   := [
                num <= tmp [+] Ox "abcd";
                  num <= tmp [-] num ; 
                  num      <= tmp      [*] arr[-1-] ;
                  num      <= arr[-1-] [/] tmp ;
                  arr[-1-] <= tmp      [|] num ;
                  num      <= tmp      [&] arr[-1-];
                  num      <= tmp      [^] num ;

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
                  arr[-1-] <=>*> (42%nat);
                  double   <=<*< (42%nat)
              ]%list;
    loop    := fun msg => [num <=  tmp [+] arr[-1-] ];
    epilogue:= []
  |}.

End TestFunction.

Definition regVars : allocation C.register [_;_] := (cr Word16 "temp", (cr Word32 "double", tt)).

Definition code := SeqCompileC.compile "testFunction" _ [_] [_] [_;_] regVars test.

Compute (layout (recover code)).