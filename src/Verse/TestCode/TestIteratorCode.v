Require Import Verse.
Require Import Verse.Arch.C.


Definition iterType := Array 10 hostE Word16.
Section TestFunction.

  Variable variable : VariableT.
  Arguments variable [k] _.
  (* The parameters of the function *)
  Variable num : variable Word16.
  Variable arr      : variable (Array 3 littleE Word16).
  Definition parameters := [Var num; Var arr].
  
  (* The local variables *)

  Definition locals : list (some type) := [].
  
  (* The temp register *)
  Variable tmp       : variable Word16.
  Variable double    : variable Word32.

  Definition registers := [Var tmp; Var double].

  Definition test : iterator iterType variable.
    verse
      {|
        (* Try out all operators *)
        setup   := [
                    MOVE tmp TO arr[- 1 -];
                    num ::= tmp [+] Ox "abcd";
                      num ::= tmp [-] num ;
                      num      ::= tmp      [*] arr[-1-] ;
                      num      ::= arr[-1-] [/] tmp ;
                      arr[-1-] ::= tmp      [|] num ;
                      num      ::= tmp      [&] arr[-1-];
                      num      ::= tmp      [^] num ;

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
                      double   ::=<*< (42%nat)
                  ]%list;
        process    := fun msg => [num ::=  tmp [+] msg[-1-] ];
        finalise := []
      |}.
  Defined.

End TestFunction.

Require Import String.

Definition regVars := (-cr Word16 "temp", cr Word32 "double"-).

Definition code : Doc + {Compile.CompileError}.
  Compile.iterator iterType "testFunction" parameters locals registers.
  assignRegisters regVars.
  statements test.
Defined.

(* Compute (tryLayout code) *)
