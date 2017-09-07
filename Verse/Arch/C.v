Require Import Verse.Word.
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
Require Import Ensembles.

Set Implicit Arguments.

Inductive creg : varT :=
  cr (ty : type) : string -> creg ty.

Module CArch <: ARCH.

  (** Name of the architecture family *)

  Definition name : string := "Portable-C".

  (** The registers for this architecture *)

  Definition register := creg.

  Definition var := machineVar register.

  Inductive typesSupported : Ensemble type :=
  | uint8           : typesSupported Word8
  | uint16          : typesSupported Word16
  | uint32          : typesSupported Word32
  | uint64          : typesSupported Word64
  | carray {n e ty} : typesSupported ty -> typesSupported (array n e ty)
  .

  Definition supportedTy := Intersection _ typesSupported wfTypes.

  Definition supportedInst := Full_set (instruction var).

  (** Encode the architecture specific restrictions on the instruction set **)

  Open Scope nat.


  Definition natToxDigit (n : nat) : ascii :=
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
    | 9 => "9"
    | 10 => "a"
    | 11 => "b"
    | 12 => "c"
    | 13 => "d"
    | 14 => "e"
    | _ => "f"
    end.

  Fixpoint writexNatAux (time n : nat) (acc : string) : string :=
    let acc' := String (natToDigit (n mod 16)) acc in
    match time with
    | 0 => acc'
    | S time' =>
      match n / 16 with
      | 0 => acc'
      | n' => writeNatAux time' n' acc'
      end
    end.

  Definition nat_to_xstr (n : nat) : string :=
    writeNatAux n n "".


  Definition callConv (paramTypes localTypes : listIn supportedTy) :
      allocation var (proj_l paramTypes ++ proj_l localTypes) :=
    (fix allStack (n : nat) l : allocation var l :=
       match l with
       | []       => tt
       | ty :: lt => (onStack n, allStack (n + 1) lt)
       end)
      0 (proj_l paramTypes ++ proj_l localTypes).

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

  Open Scope string_scope.

  Fixpoint constant_to_str {t} (td : typeDenote t) : string :=
    match t return typeDenote t -> string with
    | word n => fun bv => bitsToHex bv
    | array (S n) _ _ => fun vec => "["
                                      ++ (constant_to_str (Vector.hd vec)) ++ Vector.fold_left append EmptyString (Vector.map (fun b => "," ++ constant_to_str b) (Vector.tl vec)) ++
                                    "]"
    | _ => fun _ => ""
    end td.

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
    | @Language.constant _ ty c   => constant_to_str c
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
  Definition tab := String (ascii_of_nat 9) EmptyString.

  Definition sep_list (sep : string) (l : list string) : string :=
    fold_left append ((map (fun x => append x sep) (removelast l)) ++ [last l ""]) EmptyString.
  Definition append_list (sep : string) (l : list string) : string :=
    fold_left append (map (fun x => append x sep) l) EmptyString.

  Definition write_block (b : block var) : string :=
    append_list (";" ++ nl) (map write_inst b).

  Fixpoint ncopy (n : nat) (s : string) :=
    match n with
    | 0   => ""
    | S n => s ++ ncopy n s
    end.

  Definition var_declare {ty : type} (is_pointer : nat) (v : var ty) : string :=
    let word_type (t : type) : string :=
        match t with
        | word 0 => "uint8_t"%string
        | word 1 => "uint16_t"%string
        | word 2 => "uint32_t"%string
        | _      => ""%string
        end in
    match ty with
    | @Internal.array 1 e ty => word_type ty ++ " *" ++ write_arg (Language.var v)
    | @Internal.array n e ty => word_type ty ++ " " ++ (if is_pointer then "" else ncopy is_pointer "*") ++ write_arg (Language.var v) ++ "[" ++ nat_to_str n ++ "]"
    | _                      => word_type ty ++ " " ++ (if is_pointer then "" else ncopy is_pointer "*") ++ write_arg (Language.var v)
    end.

  Fixpoint alloc_declare (l : list type) : forall a : allocation var l, list string :=
    match l with
    | []        => fun _ => []
    | (t :: lt) => fun a : allocation var (t :: lt) => var_declare 0 (fst a) :: (alloc_declare lt (snd a))
    end.

  Definition generate {loopvar} {paramTypes localVar localReg}
             (f : Function var loopvar)
             (fa : FAllocation var paramTypes localVar localReg loopvar) : string :=
    let block  := inRegister (cr loopvar ("mesg")) in
    append_list nl [
                    "#include <stdint.h>";
                    "void " ++ Function.name f ++
                            "(" ++ var_declare 2 block ++ ", int nblocks, " ++ (sep_list "," (alloc_declare _ (pa fa))) ++ ")";
                    "{";
                    tab ++ append_list (nl ++ tab) [
                                  append_list (";" ++ nl ++ tab) (alloc_declare _ (lva fa));
                                  append_list (";" ++ nl ++ tab) (alloc_declare _ (rva fa));
                                  var_declare 0 (lv fa) ++ ";"; "" ;
                                  write_block (setup f);
                                  "while (nblocks > 0)";
                                  "{";
                                    tab ++ append_list (nl ++ tab ++ tab) [
                                                write_arg (Language.var (lv fa)) ++ " = *mesg;";
                                                write_block (loop f (lv fa));
                                                "mesg++; nblocks--;"
                                                ];
                                  "}";
                                  write_block (cleanup f)
                                ];
                    "}"
                ].
End CArch.

Module CArchAux := ArchAux CArch.
