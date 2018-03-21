Require Import Verse.Types.Internal.
Require Import Verse.Error.

Require Import Nat.

Require Import Vector.

(** * Types in verse.

There are two kinds of types supported by verse [direct] and
[memory]. A value of a direct type can potentially be stored in one of
the machine registers. The supported direct types include the word
types [Word8], [Word16] , [Word32] and [Word64] and the vector types
[Vector128 w] and [Vector256 w] where [w] is any of the above word
types.  Verse supports arrays of these direct types but arrays are
memory types.


A user is only expected to use the types exposed from this
module. There is more to types and all its gory details are exposed
from the module [Verse.Types.Internal].

*)

(** Standard word types/scalars *)
Notation Byte   := (word 0).
Notation Word8  := (word 0).
Notation Word16 := (word 1).
Notation Word32 := (word 2).
Notation Word64 := (word 3).

(* Construct an array with no alignment restriction *)
Definition Array  := array.

(* begin hide *)
Inductive BadVectorType : Prop := BadVectorTypeError.
Definition vector {k} m (t : type k) : type direct + {BadVectorType} :=
  match t with
  | word n => match compare n m with
              | LT => {- multiword (m - n) n -}
             (* | _  => error BadVectorTypeError *)
              end
  | _ => error BadVectorTypeError
  end.
(* end hide *)

Definition Vector128 (t : type direct) := recover (vector 4 t).
Definition Vector256 (t : type direct) := recover (vector 4 t).

Definition constant (ty : type direct) := StandardType.typeDenote ty.

(* An interpretation of the standard constants in a given semantics *)

Module Type CONST_SEMANTICS (W : WORD_SEMANTICS).
  Parameter constWordDenote : forall n, StandardWord.wordDenote n -> W.wordDenote n.
End CONST_SEMANTICS.

Module StandardConsts : CONST_SEMANTICS StandardWord.
  Definition constWordDenote n := @id (StandardWord.wordDenote n).
End StandardConsts.

(* To lift the interpretation of constant words to other types *)
Module ConstDenote (W : WORD_SEMANTICS) (C : CONST_SEMANTICS W).

  Module T := TypeDenote W.

  Fixpoint constDenote {ty : type direct} :=
    match ty in type direct return constant ty -> T.typeDenote ty with
    | word n        => @C.constWordDenote n
    | multiword m n => map (@C.constWordDenote n)
    end.

End ConstDenote.

(* begin hide *)
Require Import PrettyPrint.


Definition constant_doc (ty : type direct)  : constant ty -> Doc.
  refine( match ty with
          | word _         => fun w => text "0x" <> doc w
          | multiword _ _  => fun w => doc w
          end
        ); repeat simpl;  try apply vector_pretty_print.
Defined.

Global Instance constant_pretty (ty : type direct) : PrettyPrint (constant ty)
  := { doc := constant_doc ty }.
(* end hide *)
