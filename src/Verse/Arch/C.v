Require Import Arch.
Require Import Types.Internal.
Require Import Error.
Require Import Types.
Require Import Syntax.
Require Import Language.Ast.
Require Import Compile.
Require Import Language.
Require Import Word.
Require Import PrettyPrint.

Require Import String.
Require Import List.
Import ListNotations.
Require Import Vector.
Import VectorNotations.
Require Import Arith.

Set Implicit Arguments.

Definition CConstant {k} (ty : CType k) : Type :=
  match ty with
  | uint8_t     => Word.bytes 1
  | uint16_t    => Word.bytes 2
  | uint32_t    => Word.bytes 4
  | uint64_t    => Word.bytes 8
  | _           => string
  end.

Ltac notPossible := let p := fresh "p" in
                    let H := fresh "H" in
                    intro p; contradict p;
                    destruct 1 as [H]; compute in H;
                    discriminate.

Definition CConstantDenote (ty : type direct) : forall (p : noErr (typeDenote ty)),
  constant ty -> CConstant (getT p).
  refine (match ty with
          | word 0 | word 1 | word 2 | word 3 => _
          | _      => _
          end);
  first [ exact (fun _ => id) | notPossible ].
Defined.

Inductive creg : GenVariableT CType :=
| cr k (ty : CType k) : string -> creg ty.

Inductive cvar : GenVariableT CType :=
| blockPtr         : forall k (ty : CType k), cvar (CPtr ty)
| deref          : forall k (ty : CType k), cvar (CPtr ty) -> cvar ty
| counter        : cvar uint64_t
| inRegister     : forall k (ty : CType k), creg ty -> cvar ty
| functionParam  : forall k (ty : CType k), nat -> cvar ty
| onStack        : forall k (ty : CType k), nat -> cvar ty
.

Record CFrame := { cFunctionName     : string;
                   nParams : nat;
                   nLocals : nat;
                   iterateOn         : option (CType memory);
                   params            : Vector.t (some CType) nParams;
                   locals            : Vector.t (some CType) nLocals;
                   registers         : list (string * (some CType))
                }.

Module C <: ARCH.

  Definition archName : string := "Portable-C".

  Definition mType := CType.
  Definition mTypeDenote := CTypeDenote.

  Definition mConstant := @CConstant direct.
  Definition mConstantDenote := CConstantDenote.

  Definition register := creg.
  Definition mVar := cvar.

  Definition HostEndian := hostE.

  Definition Word := uint64_t.

  Definition embedRegister := inRegister.

  Definition functionDescription := CFrame.

  Definition functionPrototype cframe : Prototype CType :=
  let iterTypes := match (iterateOn cframe) with
                  | Some ty => [existT _ _ (CPtr ty); existT _ _ uint64_t]
                  | None => []
                  end%list
  in
  {|
    name := cFunctionName cframe;
    arguments := iterTypes ++ List.rev (Vector.to_list (params cframe))
  |}.

End C.

Module CFrame <: FRAME C.

  Import C.

  Definition frameState := CFrame.

  Definition emptyFrame (s : string) : frameState :=
        {| cFunctionName := s; iterateOn := None; params := []; locals := [];  registers := List.nil |}.

  Definition iterateFrame (s : string) (ty : mType memory) :=
    let state := {| cFunctionName := s; iterateOn := Some ty; params := []; locals := [];  registers := List.nil |} in
    ((existT _ _ (blockPtr ty), counter), deref (blockPtr ty), state).

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
    @newParam state k ty.


  Definition stackAlloc state ty :=
    @newLocal state ty.


  Let registerStrings state := List.map fst (registers state).

  Definition useRegister state ty (reg : creg ty ):=
      match reg with
      | cr _ nm =>
        if in_dec string_dec nm (registerStrings state)
        then None
        else Some
               {| cFunctionName := cFunctionName state;
                  iterateOn := iterateOn state;
                  params := params state;
                  locals := locals state;
                  registers := (nm , existT _ direct ty) :: registers state
               |}
      end.

  Definition description := @id CFrame.

End CFrame.

Inductive carg (Cvar : GenVariableT CType) : GenVariableT CType :=
| cv      k (ty : CType k)        : Cvar _ ty -> carg Cvar ty
| cindex  (ty : CType direct) (e : endian) b : Cvar _ (CArray b ty) -> nat -> carg Cvar ty
| cconst  (ty : CType direct)     : CConstant ty -> carg Cvar ty
.

Arguments cv [Cvar k ty] _.
Arguments cindex [Cvar ty] _ [b] _ _.
Arguments cconst [Cvar ty] _.

Instance cargDenote : argC _ CConstant carg :=
  {| mkVar   := fun Cvar k ty v => cv v;
     mkConst := fun Cvar k c => cconst c;
     mkIndex := fun Cvar b e ty p v i => cindex e v i
  |}.

Require Import Ensembles.

Inductive CAssignment :=
| Cassign3 : forall ty : CType direct, binop ->
                                       carg cvar ty -> carg cvar ty -> carg cvar ty ->
                                       CAssignment
| Cassign2 : forall ty : CType direct, uniop ->
                                       carg cvar ty -> carg cvar ty ->
                                       CAssignment
| Cupdate2 : forall ty : CType direct, binop ->
                                       carg cvar ty -> carg cvar ty ->
                                       CAssignment
| Cupdate1 : forall ty : CType direct, uniop ->
                                       carg cvar ty ->
                                       CAssignment
.

Inductive cInstruction :=
| Cincr k (ty : CType k) : carg cvar ty -> cInstruction
| Cdecr (ty : CType direct) : carg cvar ty -> cInstruction
| Cassign  : CAssignment -> cInstruction
| Citerate : cvar C.Word ->
             list cInstruction -> cInstruction
| Cnop     : cInstruction
.

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

Section PrintingInstruction.

  Instance cRegPretty : forall k (ty : CType k), PrettyPrint (creg ty)
    := { doc := fun x => match x with
                         | cr _ s => text "r" <> text s
                         end
       }.

  Fixpoint vardoc {k} (ty : CType k) (x : cvar ty) :=
    match x with
    | blockPtr ty     => text CP.blockPtrVariableName
    | deref v         => paren (text "*" <> vardoc v)
    | counter         => text "counter"
    | inRegister r    => doc r
    | functionParam _ p => text "p" <> doc p
    | onStack       _ s => text "s" <> doc s
    end.

  Global Instance cMachineVar : forall k (ty : CType k), PrettyPrint (cvar ty)
    := { doc := @vardoc _ ty }.

  Definition constant_doc (ty : CType direct)  : CConstant ty -> Doc :=
    match ty with
    | uint8_t | uint16_t | uint32_t | uint64_t
                                      => fun w => text "0x" <> doc w
    end.

  Global Instance constant_pretty (ty : CType direct) : PrettyPrint (CConstant ty)
    := { doc := constant_doc ty }.

  (** The pretty printing of our argument *)
  Fixpoint argdoc {k} (ty : CType k ) (av : carg cvar ty) :=
    match av with
    | cv v         => doc v
    | cconst c     => doc c
    | cindex _ v i => doc v <> bracket (decimal i)
    end.

  Global Instance arg_pretty_print : forall k (ty : CType k), PrettyPrint (carg cvar ty)
    := { doc := @argdoc _ _ }.

  Definition wordSize (ty : CType direct) := match ty with
                                             | uint8_t => decimal 8
                                             | uint16_t => decimal 16
                                             | uint32_t => decimal 32
                                             | uint64_t => decimal 64
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
    | bigE    => text "verse_from_be" <> wordSize ty <> (paren v)
    | _       => v
    end.

  Definition rval {ty : CType direct} (a : carg cvar ty) :=
    match a with
    | cindex e _ _ => fromMemory e ty (doc a)
    | _            => doc a
    end.

  Definition CAssign {la ra : arity} (o : op la ra) {ty : CType direct}
             (x : carg cvar ty) (y z : Doc)  :=
    let lhs := y <_> opDoc o <_> z
    in
    match x with
    | cindex e _ _ => CP.assign (doc x) (toMemory e ty lhs)
    | _                    => CP.assign (doc x) lhs
    end.

  Definition CUpdate {la ra : arity}(o : op la ra) {ty : CType direct}
             (x : carg cvar ty) (y : Doc) : Doc :=
    match x with
    | cindex _ _ _  => CAssign o x (rval x) y
    | _             => doc x <_> opDoc o <> EQUALS <_> y
    end.

  Definition CRot (ty : CType direct) (o : uniop) (a : carg cvar ty) (y : Doc)  :=
    let rvl := match o with
               | rotL n => text "verse_rotL" <> wordSize ty <> paren (commaSep [y ; decimal n])
               | rotR n => text "verse_rotR" <> wordSize ty <> paren (commaSep [y ; decimal n])
               | _      => text "BadOp"
               end
    in
    match a with
    | cindex e _ _  => CP.assign (doc a) (toMemory e ty rvl)
    | _             => CP.assign (doc a) rvl
    end.

  Global Instance assignment_C_print : PrettyPrint CAssignment | 0
    := { doc := fun assgn =>  match assgn with
                              | Cassign3 o x y z => CAssign o x (rval y) (rval z)
                              | Cupdate2 o x y   => CUpdate o x (rval y)
                              | Cassign2 u x y   =>
                                match u with
                                | bitComp  | nop => CAssign u x empty (rval y)
                                | shiftL n | shiftR n  => CAssign u x (rval y) (decimal n)
                                | rotL n   | rotR n    => CRot u x (rval y)
                                end
                              | Cupdate1 u x     =>
                                match u with
                                | bitComp  | nop => CAssign u x empty (rval x)
                                | shiftL n | shiftR n  => CUpdate u x (decimal n)
                                | rotL n   | rotR n    => CRot u x (rval x)
                                end
                              end
       }.

  Let semiEnd i := i <> text ";".
  Fixpoint show (i : cInstruction) : Doc :=
    let Cdoc b := vcat (List.map show b) in
    match i with
    | Cincr a   => semiEnd (mkDouble plus (doc a))
    | Cdecr a   => semiEnd (mkDouble minus (doc a))
    | Cassign a => semiEnd (doc a)
    | Citerate n body =>
      let loopCond := paren (doc n <_> text "> 0") in
      let nextBlock := semiSep [ CP.comment "move to next block" ] in
      (vcat [ CP.comment "Iterating over the blocks";
                CP.while loopCond (vcat [Cdoc body; nextBlock])
      ])
    | Cnop      => empty
    end
  .

  Global Instance instruction_C_print : PrettyPrint (cInstruction) | 0
    := { doc := show }.

End PrintingInstruction.

Inductive unsupportedInstruction : Prop :=
| noexmul | noeucl : unsupportedInstruction.

Module CCodeGen <: CODEGEN C.

  Import C.

  Definition mArg := carg.
  Definition mArgDenote := cargDenote.

  Definition mInstruction := cInstruction.

  Instance mInstructionDenote : instructionC cvar carg mInstruction :=
    {| UnsupportedInstruction := unsupportedInstruction;
       mkIncrement := fun ty a1 => {- Cincr a1 -};
       mkDecrement := fun ty a1 => {- Cdecr a1 -};
       mkUpdate1 := fun ty o a1 => {- Cassign (Cupdate1 o a1) -};
       mkUpdate2 := fun ty o a1 a2 => {- Cassign (Cupdate2 o a1 a2) -};
       mkAssign2 := fun ty o a1 a2 => {- Cassign (Cassign2 o a1 a2) -};
       mkAssign3 := fun ty o a1 a2 a3 => {- Cassign (Cassign3 o a1 a2 a3) -};
       mkExtassign3 := fun _ _ _ _ _ _ => error noexmul;
       mkExtassign4 := fun _ _ _ _ _ _ _ => error noeucl;
       mkMoveTo := fun b e ty p arr i v => {- Cassign (Cassign2 nop (cindex e arr i) (cv v)) -};
       mkNOP := Cnop
    |}.

  Definition loopWrapper (blockType : mType memory)
             (bVar : mVar blockType)
             (count : mVar Word)
             (body : list mInstruction) :=
    [ Citerate count (body ++ [ Cincr (cv bVar); Cdecr (cv count) ]) ]%list.

  Definition emit b := line <> vcat (List.map doc b).

  Let type_doc (t : CType direct) := text (
                                        match t with
                                        | uint8_t  => "uint8_t"%string
                                        | uint16_t => "uint16_t"%string
                                        | uint32_t => "uint32_t"%string
                                        | uint64_t => "uint64_t"%string
                                        end).

  Let Fixpoint declareArray (a : Doc)(n : nat)(ty : CType direct) :=
    match ty with
    | CArray b ty  => (declareArray a b ty) <> bracket (decimal n)
    | _            => type_doc ty <_> a <> bracket (decimal n)
    end.

  Let Fixpoint declare {k}{varty : CType k}(v : cvar varty) : Doc :=
    let vDoc := doc v in
    let fix decldoc {k} (vty : CType k) v :=
        match k as k' return CType k' -> _ with
        | direct => fun ty => type_doc ty <_> v
        | memory => fun ty => match ty with
                              | CArray b ty => declareArray v b ty
                              | CPtr ty     => decldoc ty (paren (text "*" <> vDoc))
                              end
        end vty in
    decldoc varty vDoc.

  Let Fixpoint downTo (n : nat) : Vector.t nat n :=
    match n with
    | 0%nat => []
    | S m => m :: downTo m
    end.


  Let declare_vector {n} (vec : Vector.t (some CType) n) (mapper : some CType -> nat -> Doc) :=
    Vector.to_list (Vector.map2 mapper vec (downTo n)).

  Let declare_params state :=
    let mapper := fun sty n => match sty with
                               | existT _ _ ty => declare (functionParam ty n)
                               end
    in
    let iteratorDecls := match iterateOn state with
                         | Some ty => [ declare (blockPtr ty); declare counter ]%list
                         | None    => [ ]%list
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
                text "#include <verse.h>";
                CP.voidFunction (cFunctionName state) (declare_params state);
                brace (nest 4 (line <> actualBody) <> line)
            ].

End CCodeGen.

Module Compile := Compiler C CFrame CCodeGen.
