Require Import Verse.Error.
Require Import Verse.Arch.C.
Require Import Verse.Function.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.PrettyPrint.
Require Import Verse.Word.

Require Import String.
Require Import List.
Import ListNotations.

Definition loopvar := Byte.
Definition pl      := [Ref Byte; Word16].
Definition lv      := [ArrayT 3 hostE Word16; Word16; Word32].
Definition rv      := [Word16; Word32].

Definition testVars := {| fname := "test"; param := pl; local := lv |}.

Definition lalloc : allocation (userTy C.register) lv := (onS (ArrayT 3 hostE Word16), (inR (cr Word16 "tmp"), (inR (cr Word32 "double"), tt))).

Definition test : func C.register testVars :=
  (fun v : varT =>
     fun seq : v (Ref Byte) => 
       fun num : v Word16 =>
         fun arr : v (ArrayT 3 hostE Word16) =>
           fun (tmp : v Word16) (double : v Word32) =>
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
                             arr[-1-] <=>*> (42%nat)
                         ]%list;
               loop    := [num <=  tmp [+] arr[-1-] ];
               cleanup := []
             |}, lalloc).

Definition code := CFunWrite.gen test.

Compute (layout (recover code)).
