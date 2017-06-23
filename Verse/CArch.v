Require Import Verse.Nibble.
Require Import Verse.BinTree.
Require Import Verse.Types.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Function.
Require Import Verse.Arch.
Require Import Verse.Types.Internal.
Require Import String.
Require Import Strings.Ascii.
Require Import List.
Import ListNotations.
Require Import Basics.
Require Import NPeano.

Set Implicit Arguments.

Inductive creg : varT :=
  cr (ty : type) : string -> creg ty.

Module CArch <: ARCH.

  (** Name of the architecture family *)

  Definition name : string := "C".

  (** The registers for this architecture *)

  Definition reg := creg.

  Definition var := machineVar reg.
  
  (** Encode the architecture specific restrictions on the instruction set **)

  Definition wfinstr : instruction var -> Prop := fun _ => True.
  
  Fixpoint wfinstrB (b : block var) : Prop :=
    match b with
    | [] => True
    | ih :: bt => and (wfinstr ih) (wfinstrB bt)
    end.

  Definition natToDigit (n : nat) : ascii :=
    match n with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
    end.
  Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
    let acc' := String (natToDigit (n mod 10)) acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
      | 0 => acc'
      | n' => writeNatAux time' n' acc'
      end
    end.
  Definition nat_to_str (n : nat) : string :=
    writeNatAux n n "".

  Definition callConv paramTypes localTypes : allocation var (paramTypes ++ localTypes) :=
    (fix allStack (n : nat) l : allocation var l :=
        match l with
        | []       => tt
        | ty :: lt => (onStack n, allStack (n + 1) lt)
        end)
     0 (paramTypes ++ localTypes).

    (* Allocate with loopvar being allocated in a register by user *)
  Definition allocate loopvar paramTypes localVars localReg
                  (f      : func loopvar paramTypes localVars localReg)
                  (lalloc : allocation var (loopvar :: localReg))
    : Function var loopvar * FAllocation var paramTypes localVars localReg loopvar :=

    let calloc            := callConv paramTypes localVars in
    let (palloc, lvalloc) := alloc_split var paramTypes localVars calloc in
    let lv                := fst (fst (alloc_split var (loopvar :: nil) localReg lalloc)) in
    let lralloc           := snd (alloc_split var (loopvar :: nil) localReg lalloc) in
    let f'                := fill var lralloc (fill var lvalloc (fill var palloc (f var))) in
    let fa                := {|
                               pa      := palloc;
                               lva     := lvalloc;
                               loopvar := lv;
                               rva     := lralloc;
                             |}
    in   
    pair f' fa.

  (* Allocate with loopvar being allocated on stack by callConv *)
  Definition allocate' loopvar paramTypes localVars localReg
                  (f      : func loopvar paramTypes localVars localReg)
                  (lalloc : allocation var localReg)
    : Function var loopvar * FAllocation var paramTypes localVars localReg loopvar :=

    let calloc            := callConv paramTypes (loopvar :: localVars) in
    let (palloc, ra)      := alloc_split var paramTypes (loopvar :: localVars) calloc in
    let (lva,lvalloc)     := alloc_split var (loopvar :: nil) localVars ra in
    let lv                := fst lva in
    let f'                := fill var lalloc (fill var lvalloc (fill var palloc (f var))) in
    let fa                := {|
                               pa      := palloc;
                               lva     := lvalloc;
                               loopvar := lv;
                               rva     := lalloc;
                             |}
    in   
    pair f' fa.

    (** Generate code with assurance of well formedness **)

    Definition op_to_str {a : arity} (o : op a) : string :=
      match o with
      | plus    => "+"
      | minus   => "-"
      | mul     => "*"
      | quot    => "/"
      | rem     => "%"
      | bitOr   => "|"
      | bitAnd  => "&"
      | bitXor  => "^"
      | bitComp => "~"
      | rotL _  => ""
      | rotR _  => ""
      | shiftL n => "<<" ++ (nat_to_str n)
      | shiftR n => ">>" ++ (nat_to_str n)
      end.

    Definition write_arg t (a : arg var t) : string :=
      match a with
      | Language.var v          => match v with
                                      | inRegister (cr _ st) => st
                                      | onStack n => "var" ++ (nat_to_str n)
                                   end
      | @Language.index _ 1 _ _ a _ => match a with
                                      | inRegister (cr _ st) => "*" ++ st
                                      | onStack m => "*var" ++ (nat_to_str m)
                                     end
      | Language.index a n       => match a with
                                      | inRegister (cr _ st) => st ++ "[" ++ (nat_to_str n) ++ "]"
                                      | onStack m => "var" ++ (nat_to_str m) ++ "[" ++ (nat_to_str n) ++ "]"
                                      end
      | Language.constant c         => match c with
                                      | wconst b => "0x" ++ Internal.nibblesToString (binToList _ b)
                                      | @vconst n m v => "0x" ++ fold_left append
                                                              (map
                                                                 (fun vc : Types.constant (word m) =>
                                                                    match vc with
                                                                    | wconst b => Internal.nibblesToString (binToList _ b)
                                                                    end)
                                                                 (binToList _ v))
                                                              EmptyString
                                      end
      end.

    Definition write_inst (i : instruction var) : string :=
      let 'assign a := i in
      match a with
      | assign3 b a1 a2 a3 => write_arg a1 ++ "=" ++ write_arg a2 ++ op_to_str b ++ write_arg a3
      | assign2 u a1 a2    => write_arg a1 ++ "=" ++ op_to_str u ++ write_arg a2
      | update2 b a1 a2    => write_arg a1 ++ op_to_str b ++ "=" ++ write_arg a2
      | update1 u a1       => write_arg a1 ++ op_to_str u ++ "=" ++ write_arg a1
      end.

    Definition nl := String (ascii_of_nat 10) EmptyString.
    Definition append_list (sep : string) (l : list string) : string :=
      fold_left append (map (fun x => append x sep) l) EmptyString.

    Definition write_block (b : block var) : string :=
      append_list nl (map write_inst b).

    Open Scope string_scope.
    Definition generate {loopvar} {paramTypes localVar localReg}
               (f : Function var loopvar)
               (fa : FAllocation var paramTypes localVar localReg loopvar) : string :=
      append_list nl [
                    "#include <stdint.h>";
                    "void " ++ Function.name _ _ f ++ "()"
                  ].
                            
      
      
      


  
  (**
    Translate the assignment statement to assembly. Certain assignment
    instructions can fail, for example a three address assignment like
    [A <= B + C] is not supported on a 2-address machine like x86. and
    hence the result of a translation is a [option (list mnemonic)]
    instead of just a [list mnemonics].

   *)

  (** Convert the loop statement in assembly instruction. *)
  (*Parameter loop
  : forall {b : bound}{ty : type (Bounded b)},
      var reg ty -> arg reg ty -> list mnemonic -> list mnemonic.*)

End CArch.
