Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Error.
Import Nat.
Import Basics.
Require Import NArith.

Set Implicit Arguments.

(*
(** *** Semantics of operators.

We need ways to define what an operator means. As in the case of the
semantics of types, the meaning on the operators should just lift over
from its meaning on word types. We start with the meaning of [arity].


*)

Definition arityDenote a (t : Type) :=
  match a with
  | unary   => t -> t
  | binary  => t -> t -> t
  end.


(**

This module type captures the semantics of operators for a given word
semantics. The [OpDenote] module then lifts the operator semantics on
words to all types.

 *)

(* Require Import Verse.Types.*)

Module Type OP_SEMANTICS (W : WORD_SEMANTICS).
  Parameter wordOpDenote    : forall a n, op a -> arityDenote a (W.wordDenote n).
End OP_SEMANTICS.

Module OpDenote (W : WORD_SEMANTICS)(O : OP_SEMANTICS W).

  Import O.

  Instance tyDenote : typeC TypeDenote := mkTypeDenote W.wordDenote.

  Section VectorAux.

    Variable Err : Prop.
    Variable T1 T2 T3 : Type.
    Variable m : nat.

    Local Definition opVecSplit (v : Vector.t (T1 * T2) m)
      := pair (Vector.map fst v)
              (Vector.map snd v).

    Local Definition opVecSplit2 (v : Vector.t (T1 * T2 * T3) m)
      := pair (opVecSplit (Vector.map fst v))
              (Vector.map snd v).

    Local Definition vecApply (v : Vector.t (T1 -> T2) m) := Vector.map2 apply v.

  End VectorAux.

  Local Definition liftOpDenote m typ ar : (op ar -> arityDenote ar typ) ->
                                           op ar -> arityDenote ar (Vector.t typ m) :=
    match ar return (op ar -> arityDenote ar typ) ->
                        op ar ->
                        arityDenote ar (Vector.t typ m)
    with
    | unary       => fun opD op v => Vector.map (opD op) v
    | binary      => fun opD op v1 v2 => Vector.map2 (opD op) v1 v2
    end.

  Fixpoint opDenote {ar : arity}{k : kind}(t : type k)
    : op ar -> arityDenote ar (typeDenote t) :=
    match t as t0 return op ar -> arityDenote ar (@typeDenote _ tyDenote _ t0) with
    | word n            => wordOpDenote n
    | multiword m n     => liftOpDenote (2 ^ m) (@typeDenote _ tyDenote _ (word n)) (O.wordOpDenote n)
    | array n _ tw      => liftOpDenote n (typeDenote tw) (opDenote tw)
    end.

End OpDenote.

(** We now define the semantics of the operator in the standard interpretation *)
Module StandardWordOps <: OP_SEMANTICS (StandardWord).
  Import Verse.Word.

  Definition OpError := False.

  Definition wordOpDenote ar n (o : op ar) : arityDenote  ar (StandardWord.wordDenote n) :=
    match o in op ra0 return arityDenote ra0 (StandardWord.wordDenote n) with
    | plus         => fun a b => Word.numBinOp N.add a b
    | minus        => fun a b => Word.numBinOp N.sub a b
    | mul          => fun a b => Word.numBinOp N.mul a b
    | quot         => fun a b => Word.numBinOp N.div a b
    | rem          => fun a b => Word.numBinOp N.modulo a b
    | bitOr        => fun a b => OrW a b
    | bitAnd       => fun a b => AndW a b
    | bitXor       => fun a b => XorW a b
    | bitComp      => fun a => NegW a
    | rotL    m    => fun a => RotLW m a
    | rotR    m    => fun a => RotRW m a
    | shiftL  m    => fun a => ShiftLW m a
    | shiftR  m    => fun a => ShiftRW m a
    | nop          => fun x => x
    end.

End StandardWordOps.

(** And here is the standard meaning of operations lifted to the type world *)
(*
Module StandardOps := OpDenote StandardWord StandardWordOps.
*)

*)