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
(* Require Import SeqFunction. *)

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
                   params            : Vector.t (some type) nParams;
                   locals            : Vector.t (some type) nLocals;
                   registers         : list (string * (some type))
                }.


Inductive creg : varT :=
  cr : forall k (ty : type k), string -> creg ty.

Arguments cr [k] _ _.
Inductive cvar : varT :=
| inRegister     : forall k (ty : type k), creg ty -> cvar ty
| functionParam  : forall k (ty : type k), nat -> cvar ty
| onStack        : forall k (ty : type k), nat -> cvar ty
.

Instance cRegPretty : forall k (ty : type k), PrettyPrint (creg ty)
  := { doc := fun x => match x with
                       | cr _ s => text "r" <> text s
                       end
     }.

Instance cMachineVar : forall k (ty : type k), PrettyPrint (cvar ty)
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

  Inductive typesSupported : forall k, Ensemble (type k) :=
  | uint8           : typesSupported Word8
  | uint16          : typesSupported Word16
  | uint32          : typesSupported Word32
  | uint64          : typesSupported Word64
  | carray {n e ty} : typesSupported ty -> typesSupported (array n e ty)
  .

  Fixpoint typeCheck {k}(ty : type k) : {typesSupported ty} + {~ typesSupported ty}.
    refine (match ty with
            | word 0 | word 1 | word 2 | word 3  => left _
            | array n e typ => match @typeCheck direct typ with
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
        {| cFunctionName := s; params := []; locals := [];  registers := nil |}.


  Let newParam state k ty :=
    ( @functionParam k ty (nParams state),
       {| cFunctionName := cFunctionName state;
          params := existT _ _ ty :: params state;
          locals := locals state;
          registers := registers state
       |}
    ).

  Let newLocal state k ty :=
    ( @onStack k ty (nLocals state),
      {| cFunctionName := cFunctionName state;
         params := params state;
         locals := existT _ _ ty :: locals state;
         registers := registers state
      |}
    ).


  Definition addParam state k ty :=
    _ <- when C.typeCheck ty; {- @newParam state k ty -}.


  Definition stackAlloc state k ty :=
    _ <- when C.typeCheck ty; {- @newLocal state k ty -}.


  Let registerStrings state := List.map fst (registers state).

  Definition useRegister state k ty (reg : creg ty ):=
      match reg with
      | cr _ nm =>
           if C.typeCheck ty then
            if in_dec string_dec nm (registerStrings state)
            then None
            else Some
                   {| cFunctionName := cFunctionName state;
                      params := params state;
                      locals := locals state;
                      registers := (nm , existT _ k ty) :: registers state
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

  Let type_doc (t : type direct) := text (
                                        match t with
                                        | word 0 => "uint8_t"%string
                                        | word 1 => "uint16_t"%string
                                        | word 2 => "uint32_t"%string
                                        | word 3 => "uint64_t"%string
                                        | _      => ""%string
                                        end).

  Let Fixpoint declareArray (a : Doc)(n : nat)(ty : type direct) :=
    match ty with
    | @Internal.array m _ ty => (declareArray a m ty) <> bracket (decimal n)
    | _                      => type_doc ty <_> a <> bracket (decimal n)
    end.

  Let declare {k}{varty : type k}(v : @machineVar k varty) : Doc :=
    let vDoc := doc v in
    match varty in type k0 with
    | @Internal.array 1 _ ty => let vStar := text "*" <> vDoc in
                                match ty with
                                | @Internal.array n _ ty => declareArray vStar n ty
                                | _                      => type_doc ty <_> vStar
                                end
    | @Internal.array n _ ty => declareArray vDoc n ty
    | @Internal.word  n      => type_doc (word n) <_> vDoc
    | _                      => text ""
    end.

  Let Fixpoint downTo (n : nat) : Vector.t nat n :=
    match n with
    | 0%nat => []
    | S m => m :: downTo m
    end.


  Let declare_vector {n : nat}(vec : Vector.t (some type) n) (mapper : some type -> nat -> Doc) :=
    Vector.to_list (Vector.map2 mapper vec (downTo n)).

  Let declare_params state :=
    let mapper := fun sty n => match sty with
                               | existT _ _ ty => declare (functionParam ty n)
                               end
    in List.rev (declare_vector (params state) mapper).


  Let declare_locals state :=
    let mapper := fun sty n => match sty with
                               | existT _ _ ty => declare (onStack  ty n)
                               end
    in declare_vector (locals state) mapper.

  Let declare_registers state :=
    let mapper arg := match arg with
                      | (nm, (existT _ _ typ)) => text "register" <_> (declare (inRegister (cr typ nm)))
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

  Definition loopWrapper (msgTy : type memory) (v : machineVar msgTy) (n : machineVar Word) (d : Doc) : Doc :=
    let loopCond := paren (doc n <_> text "> 0") in
    CP.while loopCond
             (
               d <> line <> CP.statements [ CP.plusplus (doc v) ;  CP.minusminus (doc n) ]
             ).

End CCodeGen.

Module CompileC := Compiler C CFrame CCodeGen.
(*
Module SeqCompileC := SeqCompiler C CFrame CCodeGen.
*)