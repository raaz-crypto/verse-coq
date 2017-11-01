Require Import Syntax.
Require Import Language.
Require Import Types.
Require Import Types.Internal.
Require Import Language.
Require Import Arch.
Require Import Compile.
Require Import Word.
Require Import Error.
Require Import PrettyPrint.

Require Import List.
Import ListNotations.
Require Import String.
Require Import Ensembles.
Require Import Program.Basics.
Require Vector.
Import Vector.VectorNotations.
Set Implicit Arguments.


Record CFrame := { cFunctionName     : string;
                   nParams : nat;
                   nLocals : nat;
                   params            : Vector.t type nParams;
                   locals            : Vector.t type nLocals;
                   registers         : list (string * type)
                }.


Inductive creg : varT :=
  cr (ty : type) : string -> creg ty.

Inductive cvar : varT :=
| inRegister     : forall ty : type, creg ty -> cvar ty
| functionParam  : forall ty : type, nat -> cvar ty
| onStack        : forall ty : type, nat -> cvar ty
.

Instance cRegPretty : forall ty, PrettyPrint (creg ty)
  := { doc := fun x => match x with
                       | cr _ s => text "r" <> text s
                       end
     }.

Instance cMachineVar : forall ty, PrettyPrint (cvar ty)
  := { doc := fun x => match x with
                       | inRegister r    => doc r
                       | functionParam _ p => text "p" <> doc p
                       | onStack       _ s => text "s" <> doc s
                       end
     }.



Module CP.

  Definition void : Doc                    := text "void".
  Definition uint_t   (n : nat)            := text "uint" <> decimal n <> text "_t".
  Definition statements                    := sepEndBy (text ";" <> line).
  Definition body b := brace (nest 4 (line <> b) <> line).
  Definition while c b := text "while" <> c <> line <> body b.
  Definition voidFunction (nm : string)
             (args : list Doc)
    := void <_> text nm <> paren (commaSep args).

  Definition register (decl : Doc) := text "register" <_> decl.
  Definition deref    v            := paren (text "*" <> v).
  Definition assign   x y          := x <_> text "=" <_> y.
  Definition plusplus d            := text "++" <> d.
  Definition minusminus d          := text "--" <> d.

End CP.


Module C <: ARCH.

  (** Name of the architecture family *)

  Definition name : string := "Portable-C".

  (** The registers for this architecture *)

  Definition register := creg.

  Definition machineVar := cvar.

  Definition Word := Word64.

  Definition embedRegister := inRegister.

  Definition supportedInst := Full_set (instruction machineVar).

  Inductive typesSupported : Ensemble type :=
  | uint8           : typesSupported Word8
  | uint16          : typesSupported Word16
  | uint32          : typesSupported Word32
  | uint64          : typesSupported Word64
  | carray {n e ty} : typesSupported ty -> typesSupported (array n e ty)
  .

  Print sumbool.
(*
  Ltac crush_tySupport :=
    match goals with
    | [ |- typesSupported (array n e ty) ] => constructor
    | [ |- typesInversion
*)
  Fixpoint typeCheck (ty : type) : {typesSupported ty} + {~ typesSupported ty}.
    refine (match ty with
            | word 0 | word 1 | word 2 | word 3  => left _
            | array n e typ => match typeCheck typ with
                               | left proof      => left (carray proof)
                               | right disproof  => right _
                               end
            | _ => right _
            end
           ); repeat constructor; inversion 1; apply disproof; trivial.
  Defined.
  Definition supportedType := typesSupported.

  Definition functionDescription := CFrame.

End C.

Module CFrame <: FRAME C.

  Import C.

  Definition frameState := CFrame.

  Definition emptyFrame (s : string) : frameState :=
        {| cFunctionName := s; params := []; locals := [];  registers := [] |}.


  Let newParam state ty :=
    ( functionParam ty (nParams state),

      {| cFunctionName := cFunctionName state;
         params := ty :: params state;
         locals := locals state;
         registers := registers state
      |}
    ).
  Let newLocal state ty :=
    ( onStack ty (nLocals state),
      {| cFunctionName := cFunctionName state;
         params := params state;
         locals := ty :: locals state;
         registers := registers state
      |}
    ).


    Definition addParam state ty :=
      _ <- when C.typeCheck ty; {- newParam state ty -}.

    Definition stackAlloc state ty :=
      _ <- when C.typeCheck ty; {- newLocal state ty -}.


    Let registerStrings state := List.map fst (registers state).
    
    Definition useRegister state  ty (reg : creg ty ):=
      match reg with
      | cr _ nm =>
           if C.typeCheck ty then
            if in_dec string_dec nm (registerStrings state)
            then None
            else Some
                   {| cFunctionName := cFunctionName state;
                      params := params state;
                      locals := locals state;
                      registers := (nm , ty) :: registers state
                   |}
          else
            None
      end.
    Definition description := @id CFrame.

End CFrame.

Module CCodeGen <: CODEGEN C.

  Import C.

  Definition emit (i : instruction (machineVar)) : Doc + { not (supportedInst i) } :=
    {- nest 4 (line <> doc i <> text ";") -}.

  Let type_doc (t : type) := text (
                                 match t with
                                 | word 0 => "uint8_t"%string
                                 | word 1 => "uint16_t"%string
                                 | word 2 => "uint32_t"%string
                                 | word 3 => "uint64_t"%string
                                 | _      => ""%string
                                 end).

  Let Fixpoint declareArray (a : Doc)(n : nat) (ty : type) :=
    match ty with
    | @Internal.array m _ ty => (declareArray a m ty) <> bracket (decimal n)
    | _                      => type_doc ty <_> a <> bracket (decimal n)
    end.
  
  Let declare {varty : type}(v : machineVar varty) : Doc :=
    let vDoc := doc v in
    match varty with
    | @Internal.array 1 _ ty => let vStar := text "*" <> vDoc in
                                match ty with
                                | @Internal.array n _ ty => declareArray vStar n ty
                                | _                      => type_doc varty <_> vStar
                                end
    | @Internal.array n _ ty => declareArray vDoc n ty
    | _                      => type_doc varty <_> vDoc
    end.

  Let Fixpoint downTo (n : nat) : Vector.t nat n :=
    match n with
    | 0%nat => []
    | S m => m :: downTo m
    end.

    
  Let declare_vector {n : nat}(vec : Vector.t type n) (mapper : type -> nat -> Doc) :=
    Vector.to_list (Vector.map2 mapper vec (downTo n)).

  Let declare_params state := List.rev (declare_vector (params state) (fun ty n => declare (functionParam ty n))).
  Let declare_locals state := declare_vector (locals state) (fun ty n => declare (onStack ty n)).

  Let declare_registers state :=
    let mapper arg := match arg with
                      | (nm, typ) => text "register" <_> (declare (inRegister (cr typ nm)))
                      end in
    List.map mapper (registers state).

  
  Definition prologue state :=
    let localDecls := vcat [ line;
                             text "/* Local variables */";
                             CP.statements (declare_locals state)
                           ] in
    let regDecls := vcat [ line;
                             text "/* Register varialbes */";
                             CP.statements (declare_registers state) ] in
    vcat  [  text "#include <stdint.h>";
               CP.voidFunction (cFunctionName state) (declare_params state);
               text "{" ;
               nest 4 (vcat [localDecls; regDecls])
          ].

  Definition epilogue := fun _ : CFrame => text "}".

  Definition loopWrapper (msgTy : type) (v : machineVar msgTy) (n : machineVar Word) (d : Doc) : Doc :=
    let loopCond := paren (doc n <_> text "> 0") in
    CP.while loopCond
             (
               d <> line <> CP.statements [ CP.plusplus (doc v) ;  CP.minusminus (doc n) ]
             ).

End CCodeGen.

Module CompileC := Compiler C CFrame CCodeGen.