Require Import Verse.
Require Import Verse.Arch.C.

Require Import Vector.
Import VectorNotations.

Section TestFunction.

  Variable variable : VariableT.

  Arguments variable [k] _.
  (* The parameters of the function *)
  Variable arr     : variable (Array 5 bigE Word16).
  Variable A B     : variable Byte.

  Definition parameters := [Var arr; Var A; Var B].

  (* The local variables *)
  Variable num      : variable Word16.

  Definition locals := [Var num].

  (* The temp register *)
  Variable tmp       : variable Word16.

  Definition registers := [Var tmp].
  Definition regAssignment := (- cr uint16_t "temp" -).
  Definition someInstruction i (_ : i < 5) : code variable.
    Import Nat.
    verse [ arr[- i -] ::=^ arr[- (i + 1) mod 5 -] ]%list.
  Defined.

  Definition testFunction : code variable.
    verse
    [ num ::= tmp + Ox "abcd";
      A   ::= A + B;
      num ::= tmp - num ;
      num      ::= tmp      * arr[-1-];
      num      ::= arr[-1-] / tmp ;
      arr[-1-] ::= tmp      | num ;
      num      ::= tmp      & arr[-1-];
      num      ::= tmp      ^ num ;
      (* binary update *)
      num ::=+ tmp;
      num ::=- arr[-1-];
      num ::=* Ox "1234";
      num ::=/ tmp;
      num ::=| tmp;
      num ::=& tmp;
      num ::=^ tmp;

      (* Unary operators *)
      num      ::=~ tmp;
      tmp      ::=  arr[-1-] <<  42;
      tmp      ::=  arr[-1-] >>  42;
      num      ::=  tmp     <*< 42;
      arr[-1-] ::=  tmp     >*> 42;

      (* Unary update operators *)
      tmp      ::=<<  (42%nat);
      tmp      ::=>>  (42%nat);
      num      ::=<*< (42%nat);
      arr[-1-] ::=>*> (42%nat);
      CLOBBER arr
    ]%list.
  Defined.

End TestFunction.

Import Compile.

Definition testcode : Doc + {Compile.CompileError}.
  Compile.function "testFunction" parameters locals registers.
  assignRegisters regAssignment.
  statements testFunction.
Defined.


Definition pgm : string := tryLayout testcode.

(*

Require Import Verse.Extraction.Ocaml.

Definition main : unit := print_code testcode.

Recursive Extraction main.

*)
