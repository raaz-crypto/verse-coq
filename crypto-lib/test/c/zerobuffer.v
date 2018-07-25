Require Import Verse.


Section ZeroBuffer.

  (* Paramterise over program variables *)
  Variable v   : VariableT.
  Arguments v [k] _.

  (* The buffer argument *)
  Variable buf : v (Array 10 bigE Word16).

  (* Define what variables are paramters, what are local variables on
    stack and what are allocated in registers *)

  Definition parameters : Declaration := [Var buf].
  Definition stack      : Declaration := [].
  Definition registers  : Declaration := [].

  (* Zero the ith entry of the buffer *)
  Definition  zeroIt (i : nat) (pf : i < 10) : code v.
    verse [ buf[- i -] ::== Ox "0000" ].
  Defined.

  (* Loop over all the indices of buffer *)
  Definition zeroBuf : code v := foreach (indices buf) zeroIt.

End ZeroBuffer.


Require Import Verse.Arch.C.

Definition code : Doc + {Compile.CompileError}.
  Compile.function "verse_zerobuf_c" parameters stack registers.
  assignRegisters (--).
  statements zeroBuf.
Defined.

(* Extracting the code

*)

Require Import Verse.Extraction.Ocaml.
Definition main : unit := print_code code.
Recursive Extraction main.
