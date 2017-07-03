Require Import String.
Require Import Verse.Tactics.
Require Import Verse.Types.Internal.

(** * Types in verse.

The verse EDSL supports the standard word types, vectors type, arrays
and sequences. The types exposed from this module is what users of
verse should stick to. There is more to types and all its gory details
of types are exposed from the module [Verse.Types.Internal].

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

Require Import Nat.

Definition constant ty := typeDenote ty.
