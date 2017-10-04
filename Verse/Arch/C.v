Require Import Syntax.
Require Import Language.
Require Import Types.
Require Import Types.Internal.
Require Import Language.
Require Import Arch.
Require Import Function.
Require Import Word.
Require Import Error.
Require Import PrettyPrint.

Require Import List.
Import ListNotations.
Require Import String.
Require Import Ensembles.
Require Import Program.Basics.

Set Implicit Arguments.

Module CP.

  Definition void : Doc                    := text "void".
  Definition uint_t   (n : nat)            := text "uint" <> decimal n <> text "_t".
  Definition statements (x : list Doc) : Doc := sepBy (text ";" <> line) x <> text ";".
  Definition body b := brace (nest 4 (line <> b) <> line).
  Definition while c b := text "while" <> c <> line <> body b.
  Definition voidFunction (nm : string)
             (args bdy : list Doc)
    := void <_> text nm <> paren (commaSep args) <> line <> body (statements bdy).
  
  Definition register (decl : Doc) := text "register" <_> decl.
  Definition deref    v            := paren (text "*" <> v).
  Definition assign   x y          := x <_> text "=" <_> y.
  Definition plusplus d            := text "++" <> d.
  Definition minusminus d          := text "--" <> d.
                                                     
End CP.


Inductive creg : varT :=
  cr (ty : type) : string -> creg ty.

Inductive cvar : varT :=
| inRegister (ty : type) : creg ty -> cvar ty
| onStack    (ty : type) : string -> cvar ty
.

Instance cRegPretty : forall ty, PrettyPrint (creg ty)
  := { doc := fun x => match x with
                       | cr _ n => text "r_" <> text n
                       end
     }.

Instance cMachineVar : forall ty, PrettyPrint (cvar ty)
  := { doc := fun x => match x with
                       | inRegister r => doc r
                       | onStack _  s => text s
                       end
     }.

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

  Definition supportedType := typesSupported.

  Record funAlloc (fv : FunVars) := fallocation
                                      {
                                        pa  : allocation machineVar (param fv);
                                        la : allocation machineVar (local fv);
                                      }.

  Definition frameDescription := { fv : FunVars & funAlloc fv }.

End C.

Module CFrame <: FRAME C.

  Import C.

  Inductive FrameError : Prop :=
  | RegisterInUse (ty : type) : register ty -> FrameError.
  
  Definition frameState := C.frameDescription.

  Definition emptyFrame (s : string) : frameState.
    refine (
        let fv := {| fname := s; param := []; local := [] |} in
        existT _ fv _
      ).
    constructor; simpl; constructor.
    Defined.
    
  Definition addParam (ty : type) (a : machineVar ty) (f : frameState) : frameState.
    refine (
  existT _ {| fname := fname (projT1 f); param := ty :: param (projT1 f); local := local (projT1 f) |} {| pa := _; la := _ |}
      ).
    simpl.
    exact ((a, pa (projT2 f))).
    exact (la (projT2 f)).
    
  Defined.

  Definition addLocal (ty : type) (a : machineVar ty) (f : frameState) : frameState.
    refine (
        existT _ {| fname := fname (projT1 f); param := param (projT1 f); local := ty :: local (projT1 f) |} {| pa := _; la := _ |}
      ).
    simpl.
    exact (pa (projT2 f)).
    exact ((a, la (projT2 f))).
  Defined.
  
  Definition paramAlloc (f : frameState) (ty : type) : (machineVar ty) * frameState + { not (In _ supportedType ty) }.
    refine (
    let n := List.length (param (projT1 f)) in
    match ty with
    | word 0 | word 1 | word 2 | word 3 | array _ _ _ =>
                                          let v := onStack ty ("l_" ++ Internal.nat_to_str n)%string in
                                          inleft (v, addParam v f)
    | _           => inright _
    end
      ).
    
    all : unfold In;
      unfold supportedType;
      unfold not; intro H; inversion H.
    Defined.

    Definition onStack (f : frameState) (ty : type) : (machineVar ty) * frameState + { not (In _ supportedType ty) }.
      refine (
    let n := List.length (param (projT1 f)) in
    match ty with
    | word 0 | word 1 | word 2 | word 3 | array _ _ _ =>
                                          let v := onStack ty ("l_" ++ Internal.nat_to_str n) in
                                          inleft (v, addLocal v f)
    | _           => inright _
    end
        ).
      all : unfold In;
        unfold supportedType;
        unfold not; intro H; inversion H.
    Defined.
      
    Definition useRegister (ty : type) (f : frameState) (r : register ty) : (machineVar ty) * frameState + { not (In _ supportedType ty) \/ FrameError }.
      refine (
          let n := List.length (param (projT1 f)) in
          match ty with
          | word 0 | word 1 | word 2 | word 3 | array _ _ _ =>
                                                let v := inRegister r in
                                                inleft (v, addLocal v f)
          | _           => inright _
          end
        ).
      
      all : unfold In;
        unfold supportedType;
        unfold not; refine (or_introl _ _);
        intro H; inversion H.
    Defined.

    Definition description : frameState -> frameDescription := id.

End CFrame.

Module CCodeGen <: CODEGEN C.

  Import C.

  Definition emit (i : instruction (machineVar)) : Doc + { not (supportedInst i) } :=
    inleft (doc i <> ";").

  Local Definition type_doc (t : type) := text (
                                              match t with
                                              | word 0 => "uint8_t"%string
                                              | word 1 => "uint16_t"%string
                                              | word 2 => "uint32_t"%string
                                              | word 3 => "uint64_t"%string
                                              | _      => ""%string
                                              end).

  Local Definition declareArray (a : Doc)(n : nat) (ty : type) := type_doc ty  <_> a <> bracket (decimal n).

  Definition declare {varty : type}(v : machineVar varty) : Doc :=
    let vDoc := doc v in
    match varty with
    | @Internal.array n _ ty => declareArray vDoc n ty
    | _                      => type_doc varty <_> vDoc
    end.

  Fixpoint alloc_declare (l : list type) : forall a : allocation machineVar l, list Doc :=
    match l with
    | []        => fun _ => []
    | (t :: lt) => fun a : allocation machineVar (t :: lt) => declare (fst a) :: (alloc_declare lt (snd a))
    end.

  Definition prologue (f : frameDescription) : Doc :=
    let 'existT _ fv fa := f in
    let localDec := alloc_declare (local fv) (la fa) in
    let paramDec := alloc_declare (param fv) (pa fa) in
    lineSep [ text "#include <stdint.h>" ;
                CP.voidFunction (fname fv) paramDec
                                localDec
            ].

  Definition epilogue : frameDescription -> Doc := fun _ => NilDoc.

  Definition loopWrapper (msgTy : type) (v : machineVar msgTy) (n : machineVar Word) (d : Doc) : Doc :=
    let loopCond := paren (doc n <_> text "> 0") in
    CP.while loopCond
             (
               d <> CP.statements [ CP.plusplus (doc v) ;  CP.minusminus (doc n) ]
             ).

End CCodeGen.

