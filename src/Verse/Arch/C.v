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
Require Import Arith.
Set Implicit Arguments.

Module CP.

  Definition void       := text "void".
  Definition uint_t n   := text "uint" <> decimal n <> text "_t".
  Definition statements := sepEndBy (text ";" <> line).
  Definition body b     := brace (nest 4 (line <> b) <> line).
  Definition while c b  := text "while" <> c <> line <> body b.

  Definition register d := text "register" <_> d.
  Definition deref    v := paren (text "*" <> v).

  Definition assign x y   := x <_> text "=" <_> y.
  Definition plusplus d   := text "++" <> d.
  Definition minusminus d := text "--" <> d.
  Definition blockPtrVariableName := "blockPtr".

  Definition voidFunction nm args
    := void <_> text nm <> paren (commaSep args).


  Section CComment.
    Variable A : Type.
    Variable APrettyPrint : PrettyPrint A.

    Definition comment (s : A)    := PrettyPrint.between ("/*    ") ("    */") (doc s).
  End CComment.
  Arguments comment [A APrettyPrint] _.
End CP.


Record CFrame := { cFunctionName     : string;
                   nParams : nat;
                   nLocals : nat;
                   iterateOn         : option (type memory);
                   params            : Vector.t (some type) nParams;
                   locals            : Vector.t (some type) nLocals;
                   registers         : list (string * (some type))
                }.


Inductive creg : VariableT :=
  cr : forall k (ty : type k), string -> creg ty.

Arguments cr [k] _ _.
Inductive cvar : VariableT :=
| blockPtr       : forall (ty : type memory), cvar ty
| counter        : cvar Word64
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
                       | blockPtr ty => paren (text "*" <> text CP.blockPtrVariableName)
                       | counter         => text "counter"
                       | inRegister r    => doc r
                       | functionParam _ p => text "p" <> doc p
                       | onStack       _ s => text "s" <> doc s
                       end
     }.

Section PrintingInstruction.

  Definition wordSize (ty : type direct) := match ty with
                                            | word w => decimal (2 ^ (w + 3))%nat
                                            | _      => text "Unsupported"
                                            end.

  Definition toMemory e ty v :=
   match e with
   | littleE => text "verse_to_le" <> wordSize ty <> (paren v)
   | bigE    => text "verse_to_be" <> wordSize ty <> (paren v)
   | _       => v
   end.

  Definition fromMemory e ty v :=
   match e with
   | littleE => text "verse_from_le" <> wordSize ty <> (paren v)
   | bigE    => text "verse_form_be" <> wordSize ty <> (paren v)
   | _       => v
   end.


  Definition rval {aK : argKind}{k} {ty : type k} (a : arg cvar aK k ty) :=
    match a with
    | @Language.Ast.index _ _ _ _ e ty _ _ => fromMemory e ty (doc a)
    | _                              => doc a
    end.

  Definition CAssign {la ra : arity}{aK : argKind}(o : op la ra) {k} {ty : type k}
             (x : arg cvar aK _ ty) (y z : Doc)  :=
    let lhs := y <_> opDoc o <_> z
    in
    match x with
    | @Language.Ast.index _ _ _ _ e ty _ _ => CP.assign (doc x) (toMemory e ty lhs)
    | _                                => CP.assign (doc x) lhs
    end.


  Definition CRot (ty : type direct) (o : uniop) (a : larg cvar _ ty) (y : Doc)  :=
    let rvl := match o with
               | rotL n => text "rotL" <> wordSize ty <> paren (commaSep [y ; decimal n])
               | rotR n => text "rotR" <> wordSize ty <> paren (commaSep [y ; decimal n])
               | _      => text "BadOp"
               end
    in
    match a with
    | @Language.Ast.index _ _ _ _ e ty _ _  => CP.assign (doc a) (toMemory e ty rvl)
    | _                                 => CP.assign (doc a) rvl
    end.

  Definition CUpdate {la ra : arity}(o : op la ra) {aK : argKind}{k} {ty : type k}
             (x : arg cvar aK _ ty) (y : Doc) :=
    match x with
    | Language.Ast.index _ _  => CAssign o  x (rval x) y
    | _                   => doc x <_> opDoc o <> EQUALS <_> y
    end.

  Global Instance assignment_C_print : PrettyPrint (assignment cvar) | 0
    := { doc := fun assgn =>  match assgn with
                              | assign3 o x y z => CAssign o x (rval y) (rval z)
                              | update2 o x y   => CUpdate o x (rval y)
                              | @assign2 _ ty u x y   =>
                                match u with
                                | bitComp  | nop => CAssign u x empty (rval y)
                                | shiftL n | shiftR n  => CAssign u x (rval y) (decimal n)
                                | rotL n   | rotR n    => CRot u x (rval y)
                                end
                              | @update1 _ ty u x      =>
                                match u with
                                | bitComp  | nop => CAssign u x empty (rval x)
                                | shiftL n | shiftR n  => CUpdate u x (decimal n)
                                | rotL n   | rotR n    => CRot u x (rval x)
                                end
                              | _ => text "BadInst"
                              end
       }.

  (*

  Definition moveToCopy {b}{e}{ty}(x : cvar (array b e ty))( i : Indices x ) (y : cvar ty)
    : assignment cvar
    := assign2 nop (Language.index x i) (var y).
*)


  Global Instance instruction_C_print : PrettyPrint (instruction cvar) | 0
    := { doc := fun i => match i with
                         | assign a => doc a
                         | moveTo x i y => doc  (assign2 nop (Language.Ast.index x i) (var y))
                         | CLOBBER a     => CP.comment (text "CLOBBER" <_> doc a)
                         end
       }.

End PrintingInstruction.


Module C <: ARCH.

  (** Name of the architecture family *)

  Definition name : string := "Portable-C".

  (** The registers for this architecture *)

  Definition register := creg.

  Definition machineVar := cvar.

  Definition HostEndian := hostE.

  Definition Word := Word64.

  Definition embedRegister := inRegister.

  Definition supportedInst := Language.Ast.supportedInst machineVar hostE.

  Definition instCheck := Language.Ast.instCheck machineVar hostE.

  Inductive typesSupported : forall k, Ensemble (type k) :=
  | uint8           : typesSupported Word8
  | uint16          : typesSupported Word16
  | uint32          : typesSupported Word32
  | uint64          : typesSupported Word64
  | carray {n e ty} : typesSupported ty -> typesSupported (Array n e ty)
  .

  Fixpoint typeCheck {k}(ty : type k) : {typesSupported ty} + {~ typesSupported ty}.
    refine (match ty with
            | word 0 | word 1 | word 2 | word 3  => left _
            | array (aligned 0) n e typ => match @typeCheck direct typ with
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
        {| cFunctionName := s; iterateOn := None; params := []; locals := [];  registers := nil |}.

  Definition iterateFrame (s : string) (ty : type memory) :=
    let state := {| cFunctionName := s; iterateOn := Some ty; params := []; locals := [];  registers := nil |} in
    _ <- when typeCheck ty; {- (blockPtr ty, counter, state) -}.

  Let newParam state k ty :=
    ( @functionParam k ty (nParams state),
      {| cFunctionName := cFunctionName state;
          iterateOn := iterateOn state;
          params := existT _ _ ty :: params state;
          locals := locals state;
          registers := registers state
       |}
    ).

  Let newLocal state ty :=
    ( @onStack direct ty (nLocals state),
      {| cFunctionName := cFunctionName state;
         iterateOn := iterateOn state;
         params := params state;
         locals := existT _ _ ty :: locals state;
         registers := registers state
      |}
    ).


  Definition addParam state k ty :=
    _ <- when C.typeCheck ty; {- @newParam state k ty -}.


  Definition stackAlloc state ty :=
    _ <- when C.typeCheck ty; {- @newLocal state ty -}.


  Let registerStrings state := List.map fst (registers state).

  Definition useRegister state ty (reg : creg ty ):=
      match reg with
      | cr _ nm =>
           if C.typeCheck ty then
            if in_dec string_dec nm (registerStrings state)
            then None
            else Some
                   {| cFunctionName := cFunctionName state;
                      iterateOn := iterateOn state;
                      params := params state;
                      locals := locals state;
                      registers := (nm , existT _ direct ty) :: registers state
                   |}
          else
            None
      end.
    Definition description := @id CFrame.

End CFrame.

Module CCodeGen <: CODEGEN C.

  Import C.

  Definition emit (i : instruction machineVar) : Doc + { not (supportedInst i) } :=
    _ <- when instCheck i; {- doc i <> text ";" -}.

  Definition sequenceInstructions ds := line <> vcat ds.

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
    | @Internal.array _ m _ ty => (declareArray a m ty) <> bracket (decimal n)
    | _                      => type_doc ty <_> a <> bracket (decimal n)
    end.

  Let declare {k}{varty : type k}(v : @machineVar k varty) : Doc :=
    let vDoc := doc v in
    match varty in type k0 with
    | @Internal.array _ n _ ty => declareArray vDoc n ty
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
    in
    let iteratorDecls := match iterateOn state with
                         | Some ty => [ declare (blockPtr ty); declare counter ]%list
                         | None    => nil%list
                         end
    in iteratorDecls ++ List.rev (declare_vector (params state) mapper).


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


  Definition makeFunction state body :=
    let localDecls := vcat [ CP.comment "Local variables";
                             CP.statements (declare_locals state)
                           ] in
    let regDecls := vcat [ CP.comment "Register variables";
                             CP.statements (declare_registers state) ] in
    let actualBody := vcat [localDecls; regDecls; body]
    in vcat [ text "#include <stdint.h>";
                CP.voidFunction (cFunctionName state) (declare_params state);
                brace (nest 4 (line <> actualBody) <> line)
            ].


  Definition loopWrapper (msgTy : type memory) (v : machineVar msgTy) (n : machineVar Word) (d : Doc) : Doc :=
    let loopCond := paren (doc n <_> text "> 0") in
    let nextBlock := semiSep [CP.plusplus (text CP.blockPtrVariableName);
                                CP.minusminus (doc n);
                                CP.comment "move to next block"
                             ] in
       (vcat [ CP.comment "Iterating over the blocks";
                 CP.while loopCond (vcat [d; nextBlock])
             ]).

End CCodeGen.

Module Compile := Compiler C CFrame CCodeGen.
