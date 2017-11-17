Require Import Verse.Error.
Require Import Verse.Arch.C.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.PrettyPrint.
Require Import Verse.Word.

Require Import String.
Require Import List.
Import ListNotations.



Section TestFunction.

  Variable variable : varT.

  Arguments variable [k] _.
  (* The parameters of the function *)
  Variable arr     : variable (array 5 hostE Word16).
  Variable A B     : variable Byte.

  Definition parameters := [Var arr; Var A; Var B].

  (* The local variables *)
  Variable num      : variable Word16.

  Definition locals := [Var num].

  (* The temp register *)
  Variable tmp       : variable Word16.

  Definition registers := [Var tmp].

  Definition testFunction : list (instruction variable) :=
    [ num <= tmp [+] Ox "abcd";
      A   <= A [+] B;
      num <= tmp [-] num ;
      num      <= tmp      [*] arr[-1-];
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
    ].

End TestFunction.

Definition ps : list (some type).
  declare parameters.
Defined.

Definition ls : list (some type).
  declare locals.
Defined.

Definition rs : list (some type).
  declare registers.
Defined.

Definition regVars : allocation C.register rs := (cr Word16 "temp", tt).
Definition code := CompileC.compile "testFunction" ps ls regVars testFunction.

Compute (recover (layout <$> code)).
