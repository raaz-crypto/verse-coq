Require Import Verse.Types.Internal.
Require Import Verse.Error.
Require Import Verse.PrettyPrint.
Import Nat.
Require Import String.
Require Import List.
Import ListNotations.
Open Scope string.

Inductive Word : Type :=
| W8       : Word
| W16      : Word
| W32      : Word
| W64      : Word
| Native   : Word
.

Instance raaz_word_prettyprint : PrettyPrint Word :=
  { doc := fun w =>
             doc ( match w with
                   | W8       => "Word8"
                   | W16      => "Word16"
                   | W32      => "Word32"
                   | W64      => "Word64"
                   | Native   => "Word"
                   end)%string
  }.

Inductive RaazType : Type :=
| RaazWord   : endian -> Word -> RaazType
| Tuple      : nat -> RaazType -> RaazType
| Ptr        : RaazType -> RaazType
| AlignedPtr : nat -> RaazType -> RaazType
.

(** Helper function to set the endianness of the word involved in the type *)
Fixpoint setEndian (e : endian)(r : RaazType) : RaazType :=
  match r with
  | RaazWord _   w => RaazWord   e w
  | Tuple      n r => Tuple      n (setEndian e r)
  | Ptr          r => Ptr          (setEndian e r)
  | AlignedPtr n r => AlignedPtr n (setEndian e r)
  end.
Inductive BDoc :=
| Atomic  : Doc  -> BDoc
| Paren   : Doc  -> BDoc
.


Instance bdoc_prettyprint : PrettyPrint BDoc :=
  { doc := fun bd => match bd with
                  | Atomic d => d
                  | Paren  d => paren d
                  end
  }.

Fixpoint bdoc (rt : RaazType) : BDoc :=
  match rt with
  | Tuple n rtp  => Paren (doc "Tuple" <_> doc n <_> doc (bdoc rtp))
  | RaazWord e w => match e with
                   | bigE    => Paren (doc "BE" <_> doc w)
                   | littleE => Paren (doc "LE" <_> doc w)
                   | _       => Atomic (doc w)
                   end
  | Ptr a => Paren (doc "Ptr" <_> doc (bdoc a))
  | AlignedPtr n a => Paren (doc "AlignPtr" <_> doc n <_> doc (bdoc a))
  end.

Instance raaztype_prettyprint : PrettyPrint RaazType :=
  { doc := fun d => match bdoc d with
                 | Atomic x => x
                 | Paren x => x
                 end
  }.



Definition ffi (fname : string)(args : list RaazType) : Doc :=
  let typD : list Doc := (List.map doc args ++ [doc "IO ()"])%list in
  let typ := match typD with
             | (y :: ys) => (doc "::" <_> y) :: List.map (fun x => doc "->" <_> x) ys
             | [] => []
             end in
  let indent := String.length fname + 1 in
  let fsig   := doc fname <_> nest indent (vcat typ) in
  nest 4 (vcat [doc "foreign import ccall unsafe"; fsig]).


Fixpoint fromCType {k}(cty : CType k) : RaazType :=
  match cty with
  | uint8_t       => RaazWord hostE W8
  | uint16_t      => RaazWord hostE W16
  | uint32_t      => RaazWord hostE W32
  | uint64_t      => RaazWord hostE W64
  | CArray n caty => match n with
                     | 1 => Ptr (fromCType caty)
                     | _ => Ptr (Tuple n (fromCType caty))
                     end
  | CPtr cty      => Ptr (fromCType cty)
  end.

Fixpoint fromMachineType {k}(mty : MachineType k) : RaazType :=
  match mty with
  | Sized n => match n with
              | 0 => RaazWord hostE W8
              | 1 => RaazWord hostE W16
              | 2 => RaazWord hostE W32
              | 3 => RaazWord hostE W64
              | _ => Tuple (n - 3) (RaazWord hostE W64)
              end
  | Address n => AlignedPtr n (RaazWord hostE W8)
  end.

Require Import Verse.Types.

Definition ccall (proto : Prototype CType) : Doc :=
  let mapper := fun scty : some CType => match scty with
                            | existT cty => fromCType cty
                            end
  in ffi (name CType proto) (List.map mapper (arguments CType proto)).

Definition asmcall (proto : Prototype MachineType) : Doc :=
  let mapper := fun scty : some MachineType => match scty with
                            | existT cty => fromMachineType cty
                            end
  in ffi (name MachineType proto) (List.map mapper (arguments MachineType proto)).
