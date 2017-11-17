Require Import String.
Require Import Verse.Types.Internal.
Require Import Verse.Error.
Require Import Nat.

(** * Types in verse.

The verse EDSL supports the standard word types, vectors type, arrays
and sequences. Users of Verse should use only types exported from this
module in their verse programs. There is more to types and all its
gory details are exposed from the module [Verse.Types.Internal].

*)

(** Standard word types/scalars *)
Definition Byte   := word 0.
Definition Word8  := word 0.
Definition Word16 := word 1.
Definition Word32 := word 2.
Definition Word64 := word 3.

Inductive BadVectorType : Prop := BadVectorTypeError.


Definition vector {k} m (t : type k) : type direct + {BadVectorType} :=
  match t with
  | word n => match compare n m with
              | LT => {- multiword (m - n) n -}
             (* | _  => error BadVectorTypeError *)
              end
  | _ => error BadVectorTypeError
  end.

Definition Vecor128 (t : type direct) := recover (vector 4 t).
Definition Vector256 (t : type direct) := recover (vector 4 t).

Definition constant {k}(ty : type k):= typeDenote ty.

Require Import PrettyPrint.


Definition constant_doc k (ty : type k)  : typeDenote ty -> Doc.
  refine( match ty with
          | word _         => fun w => text "0x" <> doc w
          | multiword _ _  => fun w => doc w
          | array _ _ _    => fun w => text ""
          end
        ); repeat simpl; apply vector_pretty_print.
Defined.

Global Instance constant_pretty k  (ty : type k) : PrettyPrint (constant ty)
  := { doc := constant_doc k ty }.
