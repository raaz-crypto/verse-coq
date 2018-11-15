Require Import Verse.
Require Import Verse.Arch.C.
Require Import Verse.Types.Internal.
Require Import Semantics.

Import StandardSemantics.
Open Scope word_scope.

Import NArith.
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
  Definition someInstruction i (_ : i < 5) : code variable.
    Import Nat.
    verse [ arr[- i -] ::=^ arr[- (i + 1) mod 5 -] ]%list.
  Defined.

  Definition testFunction : code variable.
    verse
      [ num ::= tmp [+] Ox "abcd";

        ASSERT num HAD n ; tmp HAS t IN n = (RotR t 2) XOR n;

        ASSERT A HAS a; num HAD n ; tmp HAD t IN (n = t) /\ (t = n);

        A   ::= A [+] B;
        num ::= tmp [-] num ;

        ASSERT num HAD n ; tmp HAS t IN n = t;
        ASSERT num HAS n IN (n = n);

        ASSERT num HAD n' ; num HAS n IN (n = n')%N;

        ASSERT num HAD n' ; num HAS n IN (n = n')%N;

        ASSERT A HAS a IN (2 = 3)%N;

        arr[-1-] ::== num;
        num      ::= tmp      [*] arr[-1-];

        ASSERT num HAD n ; tmp HAS t ; A HAS a IN (and (n = t) (n = n))%N;

        num      ::= arr[-1-] [/] tmp ;

        (* binary update *)
        num ::=+ tmp;
        num ::=- arr[-1-];
        num ::=* Ox "1234";
        num ::=/ tmp;

        ASSERT num HAD n ; tmp HAD t ; num HAS n' IN
               (and (n' = t) (n' = n))%N;

        CLOBBER arr
      ]%list.
  Defined.

End TestFunction.

Import StandardTactics.
(*
Inductive var : VariableT :=
| arr : var (Array 5 bigE Word16)
| A : var Byte
| B : var Byte
| num : var Word16
| tmp : var Word16
.

Definition var_eqb {k} {ty : type k} (v1 v2 : var ty) : bool :=
  match v1, v2 with
  | arr, arr => true
  | A, A     => true
  | B, B
  | num, num
  | tmp, tmp => true
  | _, _     => false
  end.
 *)

Definition toProve : Prop.
  extractSAT testFunction.
Defined.

(* A potential proof template *)

Definition proof : toProve.
  time (
  unfold toProve;
  unfold genSAT;
  unfold SAT;
  breakStore;
  lazy -[RotRW RotLW ShiftRW ShiftLW XorW AndW OrW NegW
              fromNibbles
              numBinOp numUnaryOp numBigargExop numOverflowBinop
              Nat.add Nat.sub Nat.mul Nat.div
              N.add N.sub N.mul N.div N.div_eucl N.modulo
              Ox nth replace]).
Abort.

Import Compile.

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
