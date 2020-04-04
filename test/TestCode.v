Require Import Nat.
Require Import NArith.
Require Import Verse.
Require Import Verse.Nibble.
Require Import String.
Open Scope string_scope.
Import List.ListNotations.
Section TestFunction.

  Variable variable : VariableT.

  Arguments variable [k] _.
  (* The parameters of the function *)
  Variable arr     : variable (array 5 bigE Word16).
  Variable A B     : variable Byte.


  (* Definition parameters := [Var arr; Var A; Var B]. *)

  (* The local variables *)
  Variable num      : variable Word16.

  (*
  Definition locals := [Var num]. *)

  (* The temp register *)
  Variable tmp       : variable Word16.

  (* Definition registers := [Var tmp]. *)


  (* Definition regAssignment := (- cr uint16_t "temp" -). *)
  Definition someInstruction i (_ : i < 5) : code variable.
    verse [ arr[- i -] ::=x arr[- (i + 1) mod 5 -] + tmp + 1]%list.
  Defined.


  Definition stmt1 : statement variable := num ::= Ox "1234".
  Definition stmt2 : statement variable := num ::=* Ox "abcd".
  Definition stmt3 : statement variable := num ::= num * Ox "12 34".


  Definition testFunction : code variable.
    verse
      [  (* Assignments  using binary operators *)
        num ::= tmp + 43981%N;
        A   ::= A + B;
        num ::= tmp - num ;
        num      ::= tmp      * arr[-1-];
        num      ::= arr[-1-] / tmp ;
        arr[-1-] ::= tmp  OR num ;
        num      ::= tmp  XOR arr[-1-];
        num      ::= tmp  XOR num;

       (* Assignments using unary operators *)

        num      ::= neg tmp;
        tmp      ::=  arr[-1-] <<  42;
        tmp      ::=  arr[-1-] >>  42;
        num      ::=  tmp     <<< 42;
        arr[-1-] ::=  tmp     >>> 42;

        (* binary update *)

        num ::=+ tmp;
        num ::=- arr[-1-];
        num ::=* 2;
        num ::=/ tmp;
        num ::=| 5;
        num ::=& tmp;
        num ::=x tmp;

      (* Unary update operators *)
        tmp      ::=<<  (42%nat);
        tmp      ::=>>  (42%nat);
        num      ::=<<< (42%nat);
        arr[-1-] ::=>>> (42%nat)
    ]%list.
  Defined.

  Print testFunction.
End TestFunction.

(*
Import Compile.

Definition testcode : Doc + {Compile.CompileError}.
  Compile.function "testFunction" parameters locals registers.
  assignRegisters regAssignment.
  statements testFunction.
Defined.


Definition pgm : string := tryLayout testcode.
*)
(*

Require Import Verse.Extraction.Ocaml.

Definition main : unit := print_code testcode.

Recursive Extraction main.

*)
