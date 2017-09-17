Require Import String.
Require Import Verse.Types.Internal.

(** * Types in verse.

The verse EDSL supports the standard word types, vectors type, arrays
and sequences. Users of Verse should use only types exported from this
module in their verse programs. There is more to types and all its
gory details are exposed from the module [Verse.Types.Internal]. Using
the internal module directly can lead to creation of non-well formed
types and hence is discouraged.

*)

(** Standard word types/scalars *)
Definition Byte   : type := WordT 0.
Definition Word8  : type := WordT 0.
Definition Word16 : type := WordT 1.
Definition Word32 : type := WordT 2.
Definition Word64 : type := WordT 3.



(** Standard vector types *)
Definition Vector128_64   : type := VectorT 1 Word64.
Definition Vector128_32   : type := VectorT 2 Word32.
Definition Vector128_16   : type := VectorT 3 Word16.
Definition Vector128_8    : type := VectorT 4 Word8.
Definition Vector128Bytes : type := VectorT 4 Byte.

Definition Vector256_64   : type := VectorT 2 Word64.
Definition Vector256_32   : type := VectorT 3 Word32.
Definition Vector256_16   : type := VectorT 4 Word16.
Definition Vector256_8    : type := VectorT 5 Word8.
Definition Vector256Bytes : type := VectorT 5 Byte.

(** The reference type. We use array of size 1 for reference types *)
Definition Ref (ty : type) := array 1 hostE ty.

Require Import Nat.

Definition constant ty := typeDenote ty.

Require Import PrettyPrint.

Fixpoint constant_doc (ty : type) : constant ty -> Doc :=
  match ty as ty0 return constant ty0 -> Doc with
  | word n => fun w => text "0x" <> doc w
  | _      => fun _ => text ""
  end.

Instance constant_pretty {ty : type} : PrettyPrint (constant ty) := { doc := constant_doc ty}.
