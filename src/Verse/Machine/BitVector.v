(** * Bit vector semantics.

This module exposes a semantics that is based on interpreting the
words as bitvectors.

*)

Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Language.Pretty.
Require Import Verse.BitVector.

Definition wordOfSize : nat -> Type := Types.BWord.

Definition const : forall sz : nat, constOf verse_type_system (word sz) -> wordOfSize sz
  := fun sz x => x.

Definition oper (sz arity : nat) (o : op arity)
  := match o in op arity0 return nary (wordOfSize sz) arity0 with
     | plus      => addition
     | minus     => subtraction
     | mul       => multiplication
     | quot      => @BVquot    _
     | rem       => @BVrem     _
     | bitOr     => Or
     | bitAnd    => And
     | bitXor    => Xor
     | bitComp   => Not
     | shiftL  n => @BVshiftL  _ n
     | shiftR  n => @BVshiftR  _ n
     | rotL    n => @BVrotL    _ n
     | rotR    n => @BVrotR    _ n
     end.

Definition bvDenote : typeDenote verse_type_system := fromWordDenote wordOfSize const oper.
