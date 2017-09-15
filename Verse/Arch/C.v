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
Require Import Verse.PrettyPrint.

Set Implicit Arguments.

Module CP.

  Definition void : Doc                    := text "void".
  Definition uint_t   (n : nat)            := text "uint" <> decimal n <> text "_t".
  Definition statements (x : list Doc) : Doc := sepBy (text ";" <> line) x <> text ";".
  Definition body b := brace (nest 4 (line <> statements  b) <> line).
  Definition while c b := text "while" <> c <> line <> body b.
  Definition voidFunction (nm : string)
             (args bdy : list Doc)
    := void <_> text nm <> paren (commaSep args) <> line <> body bdy.
  
  Definition register (decl : Doc) := text "register" <_> decl.
  Definition deref    v            := text "*" <> v.
  Definition assign   x y          := x <_> text "=" <_> y.
  Definition plusplus d            := text "++" <> d.
  Definition minusminus d          := text "--" <> d.
                                                     
End CP.
                                                           
                                                                 
Inductive creg : varT :=
  cr (ty : type) : string -> creg ty.

Instance cRegPretty : forall ty, PrettyPrint (creg ty)
  := { doc := fun x => match x with
                       | cr _ n => text "r_" <> text n
                       end
     }.

Instance cMachineVar : forall ty, PrettyPrint (machineVar creg ty)
  := { doc := fun x => match x with
                       | inRegister r => doc r
                       | onStack    n => text "l_" <> decimal n
                       end
     }.

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

  Definition callConv (paramTypes localTypes : listIn supportedTy) :
    allocation var (proj_l paramTypes ++ proj_l localTypes) :=
    (fix allStack (n : nat) l : allocation var l :=
       match l with
       | []       => tt
       | ty :: lt => (onStack n, allStack (n + 1) lt)
       end)
      0%nat (proj_l paramTypes ++ proj_l localTypes).

  (** Generate code with assurance of well formedness **)


  Open Scope string_scope.

  Local Definition type_doc (t : type) := text (
                                              match t with
                                              | word 0 => "uint8_t"%string
                                              | word 1 => "uint16_t"%string
                                              | word 2 => "uint32_t"%string
                                              | word 3 => "uint64_t"%string
                                              | _      => ""%string
                                              end).
  Local Definition declareArray (a : Doc)(n : nat) (ty : type) := type_doc ty  <_> a <> bracket (decimal n).

  Local Definition declareSeq   (seqty : type) (v : Doc) :=
    let pointerToV := text "*" <> v in
        match seqty with
        | array n e ty => declareArray (paren pointerToV) n ty
        | _            => type_doc seqty <_> pointerToV
        end.


  Definition declare {varty : type}(v : var varty) : Doc :=
    let vDoc := doc v in
    match varty with
    | @Internal.array n _ ty => declareArray vDoc n ty
    | _                      => type_doc varty <_> vDoc
    end.

  Fixpoint alloc_declare (l : list type) : forall a : allocation var l, list Doc :=
    match l with
    | []        => fun _ => []
    | (t :: lt) => fun a : allocation var (t :: lt) => declare (fst a) :: (alloc_declare lt (snd a))
    end.


  Definition generate {seqType} {paramTypes localVar localReg}
             (f : Function var seqType)
             (fa : FAllocation var paramTypes localVar localReg seqType) : Doc :=
    let seqVar   := text "seqVar" in
    let countVar := text "nElem"  in
    let seqVarDec   := declareSeq seqType seqVar in
    let countVarDec := text "int" <_> countVar in
    let paramDec := alloc_declare paramTypes (pa fa) in
    let arguments := seqVarDec :: countVarDec :: paramDec in
    let loopCond := paren (countVar <_> text "> 0") in
    let localDec := alloc_declare localVar (lva fa) in
    let regDec   := List.map CP.register (alloc_declare localReg (rva fa)) in
    lineSep [ text "#include <stdint.h>" ;
                CP.voidFunction (Function.name f) arguments
                                (localDec ++ regDec ++ List.map doc (setup f)
                                         ++ [ CP.while loopCond
                                                       (
                                                         [ CP.assign (doc (lv fa)) (CP.deref seqVar) ]
                                                           ++ List.map doc (loop f (lv fa))
                                                           ++ [ CP.plusplus seqVar ;  CP.minusminus countVar ]
                                                       )
                                            ]
                                         ++ List.map doc (cleanup f)
                                )%list
                   
            ].
End CArch.

Module CArchAux := ArchAux CArch.
