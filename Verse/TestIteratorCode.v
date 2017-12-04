Require Import Verse.Error.
Require Import Verse.Arch.C.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.PrettyPrint.
Require Import Verse.Word.
Require Import Verse.Compile.

Require Import String.
Require Import List.
Import ListNotations.

Definition iterType := array 10 hostE Word16.
Section TestFunction.

  Variable variable : varT.
  Arguments variable [k] _.
  (* The parameters of the function *)
  Variable num : variable Word16.
  Definition parameters := [Var num].

  (* The local variables *)
  Variable arr      : variable (array 3 hostE Word16).

  Definition locals := [Var arr].
  (* The temp register *)
  Variable tmp       : variable Word16.
  Variable double    : variable Word32.

  Definition registers := [Var tmp; Var double].
                            
  Definition test : iterator iterType variable :=
  {|
    (* Try out all operators *)
    setup   := [
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
    process    := fun msg => [num <=  tmp [+] msg[-1-] ];
    finalise := []
  |}.

End TestFunction.


Definition regVars := (cr Word16 "temp", (cr Word32 "double", tt)).

Definition code : Doc + {Compile.CompileError}.
  CompileC.iterator iterType "testFunction".
     declare parameters.
     declare locals.
     declare registers.
     exact regVars.
     exact test.
Defined.

Compute (layout (recover code)).