Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Error.
Import Nat.
Import Basics.
Require Import NArith.

Set Implicit Arguments.

(** * Arithmetic and bitwise operators.

Most architectures allow various basic arithmetic and bitwise
operations on values stored in the registers. These operations can be
either [unary] or [binary].

*)

Inductive arity  := binary | unary | ternary.

Inductive op    : arity -> arity -> Type :=
| plus    : op unary binary
| minus   : op unary binary
| mul     : op unary binary
| exmul   : op binary binary
| quot    : op unary binary
| rem     : op unary binary
| eucl    : op binary ternary
| bitOr   : op unary binary
| bitAnd  : op unary binary
| bitXor  : op unary binary
| bitComp : op unary unary
| rotL    : nat -> op unary unary
| rotR    : nat -> op unary unary
| shiftL  : nat -> op unary unary
| shiftR  : nat -> op unary unary
| nop     : op unary unary
.

Notation simop := (op unary).
Notation exop  := (op binary).
Notation binop := (simop binary).
Notation uniop := (simop unary).
Notation triop := (simop ternary).

(** *** Semantics of operators.

We need ways to define what an operator means. As in the case of the
semantics of types, the meaning on the operators should just lift over
from its meaning on word types. We start with the meaning of [arity].


*)

Local Definition lArityDenote Err a t : Type  :=
  let t' := t + {Err} in
  match a with
  | unary    => t'
  | binary   => t' * t'
  | ternary  => t' * t' * t'
  end.

Definition arityDenote Err la ra (t : Type) :=
  let dest := lArityDenote Err la t in
  match ra with
  | unary   => t -> dest
  | binary  => t -> t -> dest
  | ternary => t -> t -> t -> dest
  end.


(**

This module type captures the semantics of operators for a given word
semantics. The [OpDenote] module then lifts the operator semantics on
words to all types.

 *)

(* Require Import Verse.Types.*)

Module Type OP_SEMANTICS (W : WORD_SEMANTICS).
  Parameter OpError : Prop.
  Parameter wordOpDenote    : forall la ra n, op la ra -> arityDenote OpError la ra (W.wordDenote n).
End OP_SEMANTICS.

Module OpDenote (W : WORD_SEMANTICS)(O : OP_SEMANTICS W).

  Import O.

  Instance tyDenote : typeC TypeDenote := mkTypeDenote W.wordDenote.

  Section VectorAux.

    Variable Err : Prop.
    Variable T1 T2 T3 : Type.
    Variable m : nat.

    Local Fixpoint liftErr T m (v : Vector.t (T + {Err}) m) :=
      match v with
      | Vector.nil _ => {- Vector.nil _ -}
      | Vector.cons _ t _ vt => t' <- t; Vector.cons _ t' _ <$> (liftErr vt)
      end.

    Local Definition opVecSplit v := pair (@liftErr T1 m (Vector.map fst v))
                                          (@liftErr T2 m (Vector.map snd v)).

    Local Definition opVecSplit2 v := pair (opVecSplit (Vector.map fst v))
                                           (@liftErr T3 _ (Vector.map snd v)).

    Local Definition vecApply (v : Vector.t (T1 -> T2) m) := Vector.map2 apply v.

  End VectorAux.

  Local Definition liftOpDenote m typ la ra : (op la ra -> arityDenote OpError la ra typ) ->
                                              op la ra -> arityDenote OpError la ra (Vector.t typ m) :=
    match la, ra return (op la ra -> arityDenote OpError la ra typ) ->
                        op la ra ->
                        arityDenote OpError la ra (Vector.t typ m)
    with
    | unary, unary       => fun opD op v => liftErr (Vector.map (opD op) v)
    | binary, unary      => fun opD op v =>  (opVecSplit (Vector.map (opD op) v))
    | ternary, unary     => fun opD op v => (opVecSplit2 (Vector.map (opD op) v))
    | unary, binary      => fun opD op v1 v2 => liftErr (Vector.map2 (opD op) v1 v2)
    | binary, binary     => fun opD op v1 v2 => (opVecSplit (Vector.map2 (opD op) v1 v2))
    | ternary, binary    => fun opD op v1 v2 => (opVecSplit2 (Vector.map2 (opD op) v1 v2))
    | unary, ternary     => fun opD op v1 v2 v3 => liftErr (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3)
    | binary, ternary    => fun opD op v1 v2 v3 =>  (opVecSplit (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3))
    | ternary, ternary   => fun opD op v1 v2 v3 =>  (opVecSplit2 (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3))
    end.

  Fixpoint opDenote {la ra : arity}{k : kind}(t : type k)
    : op la ra -> arityDenote OpError la ra (typeDenote t) :=
    match t as t0 return op la ra -> arityDenote OpError la ra (@typeDenote _ tyDenote _ t0) with
    | word n            => wordOpDenote n
    | multiword m n     => liftOpDenote (2 ^ m) (@typeDenote _ tyDenote _ (word n)) (O.wordOpDenote n)
    | array n _ tw      => liftOpDenote n (typeDenote tw) (opDenote tw)
    end.

End OpDenote.

(** We now define the semantics of the operator in the standard interpretation *)
Module StandardWordOps <: OP_SEMANTICS (StandardWord).
  Import Verse.Word.

  Definition OpError := False.

  Definition wordOpDenote la ra n (o : op la ra) : arityDenote OpError la ra (StandardWord.wordDenote n) :=
    match o in op la0 ra0 return arityDenote OpError la0 ra0 (StandardWord.wordDenote n) with
    | plus         => fun a b => {- Word.numBinOp N.add a b -}
    | minus        => fun a b => {- Word.numBinOp N.sub a b -}
    | mul          => fun a b => {- Word.numBinOp N.mul a b -}
    | exmul        => fun a b => Word.mapP inleft (Word.numOverflowBinop N.mul a b)
    | quot         => fun a b => {- Word.numBinOp N.div a b -}
    | eucl         => fun a b c => Word.mapP inleft (Word.numBigargExop N.div_eucl a b c)
    | rem          => fun a b => {- Word.numBinOp N.modulo a b -}
    | bitOr        => fun a b => {- OrW (8 * 2^n) a b -}
    | bitAnd       => fun a b => {- AndW  (8 * 2^n) a b -}
    | bitXor       => fun a b => {- XorW (8 * 2^n) a b -}
    | bitComp      => fun a => {- NegW (8 * 2^n) a -}
    | rotL    m    => fun a => {- RotL m (8 * 2^n) a -}
    | rotR    m    => fun a => {- RotR m (8 * 2^n) a -}
    | shiftL  m    => fun a => {- ShiftL m (8 * 2^n) a -}
    | shiftR  m    => fun a => {- ShiftR m (8 * 2^n) a -}
    | nop          => fun x => {- x -}
    end.

End StandardWordOps.

(** And here is the standard meaning of operations lifted to the type world *)
(*
Module StandardOps := OpDenote StandardWord StandardWordOps.
*)