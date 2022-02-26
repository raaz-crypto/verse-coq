From Verse Require Import Verse Nibble.
Require Import Nat.
Require Import NArith.
Import VerseNotations.
Require Import String.
Open Scope string_scope.
Import List.ListNotations.
Section TestFunction.

  Variable variable : VariableT.

  (* The parameters of the function *)
  Variable arr     : variable (existT _ _ (array 5 bigE Word16)).
  Variable A B     : variable (existT _ _ Byte).


  (* Definition parameters := [Var arr; Var A; Var B]. *)

  (* The local variables *)
  Variable num      : variable (existT _ _ Word16).

  (*
  Definition locals := [Var num]. *)

  (* The temp register *)
  Variable tmp       : variable (existT _ _ Word16).

  (* Definition registers := [Var tmp]. *)


  (* Definition regAssignment := (- cr uint16_t "temp" -). *)
  Definition someInstruction i (_ : i < 5) : code variable.
    verse [code| arr[ i ] ⊕= arr[ ` (i + 1) mod 5` ] + tmp + `1` |].
  Defined.


  Definition stmt1 : statement variable := [verse| num := `Ox "1234"` |].
  Definition stmt2 : statement variable := [verse| num *= `Ox "abcd"` |].
  Definition stmt3 : statement variable := [verse| num := num * `Ox "12 34"` |].


  Definition testFunction : code variable.
    verse
      [code|  (* Assignments  using binary operators *)
        num := tmp + `43981%N`;
        A   := A + B;
        num := tmp - num ;
        num      := tmp      * arr[ `1` ];
        num      := arr[ `1` ] / tmp ;
        arr[ `1` ] := tmp  | num ;
        num      := tmp  ^ arr[`1`]; (* ascii version of XOR operator *)
        num      := tmp  ⊕ num;      (* Unicode version of XOR operator *)

        (* Assignments using unary operators, Ascii version and unicode version *)

        num       := ~ tmp;
        tmp       :=  arr[`1`] <<  `42`;
        tmp       :=  arr[`1`] ≪  `42`;

        tmp       :=  arr[`1`] >> `42`;
        tmp       :=  arr[`1`] ≫  `42`;

        num       :=  tmp     <<< `42`;
        num       :=  tmp     ⋘ `42`;

        arr[ `1`] :=  tmp     >>> `42`;
        arr[ `1`] :=  tmp     ⋙  `42`;

        (* binary update *)

        num += tmp;
        num -= arr[`1`];
        num *= `2`;
        num /= tmp;
        num |= `5`;
        num &= tmp;
        num ^= tmp;
        num ⊕= tmp;

      (* Unary update operators *)
        tmp      <<=  (`42%nat`);
        tmp      ≪=  (`42%nat`);
        tmp      >>=  (`42%nat`);
        tmp      ≫=  (`42%nat`);
        num      <<<= (`42%nat`);
        num      ⋘= (`42%nat`);
        arr[`1`] >>>= (`42%nat`);
        arr[`1`] ⋙= (`42%nat`)
    |].
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
