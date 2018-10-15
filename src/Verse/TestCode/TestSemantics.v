Require Import Verse.
Require Import Verse.Arch.C.
Require Import Types.Internal.

Require Import NSemantics.
Import NSemantics.

Require Import NArith.
Require Import Vector.
Import VectorNotations.

Set Implicit Arguments.


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
  Definition someInstruction i (_ : i < 5) : Code variable.
    Import Nat.
    verse [ arr[- i -] ::=^ arr[- (i + 1) mod 5 -] ]%list.
  Defined.

  Definition testFunction : code variable.
    verse
    [ num ::= tmp [+] Ox "abcd";

              ASSUME num <== n ; tmp <== t IN n = t;

      A   ::= A [+] B;
      num ::= tmp [-] num ;

              CLAIM num <== n IN n = 0%N;
              ASSUME A <== a IN (a > 0)%N;

      num      ::= tmp      [*] arr[-1-];

              CLAIM num <== n ; tmp <== t IN n = t;

      num      ::= arr[-1-] [/] tmp ;

      (* binary update *)
      num ::=+ tmp;
      num ::=- arr[-1-];
      num ::=* Ox "1234";
      num ::=/ tmp;

      CLOBBER arr
    ]%list.
  Defined.

End TestFunction.

Definition toProve : Prop.

  extractProp testFunction.

Defined.

(* A potential proof template *)
Definition proof : toProve.

  NSemantics.simplify.

  unfold NWord.wordDenote in *.
  intuition.
Abort.  
  
Import Compile.

Set Printing Implicit.
Definition testcode : Doc + {Compile.CompileError}.
  Compile.function "testFunction" parameters locals registers.
  assignRegisters regAssignment.
  statements testFunction.
Defined.

Compute (tryLayout testcode).

(*

Require Import Verse.Extraction.Ocaml.

Definition main : unit := print_code testcode.

Recursive Extraction main.

*)
