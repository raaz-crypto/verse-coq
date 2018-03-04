Require Import Verse.Types.
Require Import Verse.Types.Internal.
Import Nat.
Import Basics.
Require Import NArith.

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

Definition ArityDenote (a : arity) t :=  match a with
                                         | binary => t -> t -> t
                                         | unary  => t -> t
                                         end.


(**

This module type captures the semantics of operators for a given word
semantics. The [OpDenote] module then lifts the operator semantics on
words to all types.

 *)

(* Require Import Verse.Types.*)

Module Type OP_SEMANTICS(W : WORD_SEMANTICS).
  Parameter wordOpDenote    : forall a n, op a  -> ArityDenote a (W.wordDenote n).
End OP_SEMANTICS.

Module OpDenote (W : WORD_SEMANTICS)(O : OP_SEMANTICS W).

  Module T := TypeDenote W.

  Local Definition liftOpDenote m typ : forall a, (op a -> ArityDenote a typ)
                                                    -> op a -> ArityDenote a (Vector.t typ m) :=
    fun a => match a with
             | binary => fun opD (op : op binary) => Vector.map2 (opD op)
             | unary  => fun opD (op : op unary)  => Vector.map  (opD op)
             end.

  Fixpoint opDenote {a : arity}{k : kind}(t : type k) : op a -> ArityDenote a (T.typeDenote t) :=
    match t as t0 return op a -> ArityDenote a (T.typeDenote t0) with
    | word n => O.wordOpDenote a n
    | multiword m n   => liftOpDenote (2 ^ m) (T.typeDenote (word n)) a (O.wordOpDenote a n)
    | array _ n _ tw    => liftOpDenote n (T.typeDenote tw) a (opDenote tw)
    end.

  Arguments opDenote [a k] t  _.
End OpDenote.

(** We now define the semantics of the operator in the standard interpretation *)
Module StandardWordOps : OP_SEMANTICS (StandardWord).
  Import Verse.Word.
  Definition wordOpDenote a n (o : op a) :=
    match o in op a0 return ArityDenote a0 (StandardWord.wordDenote n) with
    | plus         => Word.numBinOp N.add
    | minus        => Word.numBinOp N.sub
    | mul          => Word.numBinOp N.mul
    | quot         => Word.numBinOp N.div
    | rem          => Word.numBinOp N.modulo
    | bitOr        => AndW (8 * 2^n)
    | bitAnd       => OrW  (8 * 2^n)
    | bitXor       => XorW (8 * 2^n)
    | bitComp      => NegW (8 * 2^n)
    | rotL    m    => RotL m (8 * 2^n)
    | rotR    m    => RotR m (8 * 2^n)
    | shiftL  m    => ShiftL m (8 * 2^n)
    | shiftR  m    => ShiftR m (8 * 2^n)
    | nop          => fun x => x
    end.

End StandardWordOps.

(** And here is the standard meaning of operations lifted to the type world *)
Module StandardOps := OpDenote StandardWord StandardWordOps.
