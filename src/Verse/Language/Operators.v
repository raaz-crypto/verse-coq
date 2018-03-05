Require Import Verse.Types.
Require Import Verse.Types.Internal.
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

Definition LArityDenote a t : Type  := match a with
                                       | unary    => t
                                       | binary   => t * t
                                       | ternary  => t * t * t
                                       end.

Definition ArityDenote larity rarity (t : Type) :=
  let dest := LArityDenote larity t in
  match rarity with
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
  Parameter wordOpDenote    : forall la ra n, op la ra -> ArityDenote la ra (W.wordDenote n).
End OP_SEMANTICS.

Module OpDenote (W : WORD_SEMANTICS)(O : OP_SEMANTICS W).

  Module T := TypeDenote W.

  Local Definition vecSplit T1 T2 m (v : Vector.t (T1 * T2) m) :=
    (Vector.map fst v, Vector.map snd v).

  Local Definition vecSplit2 T1 T2 T3 m (v : Vector.t (T1 * T2 * T3) m) :=
    (vecSplit (Vector.map fst v), Vector.map snd v).

  Local Definition vecApply T1 T2 m (v : Vector.t (T1 -> T2) m) := Vector.map2 apply v.

  Local Definition liftOpDenote m typ la ra : (op la ra -> ArityDenote la ra typ) ->
                                              op la ra -> ArityDenote la ra (Vector.t typ m) :=
    match la, ra return (op la ra -> ArityDenote la ra typ) -> op la ra -> ArityDenote la ra (Vector.t typ m) with
    | unary, unary   => fun opD op v => Vector.map (opD op) v
    | binary, unary  => fun opD op v => vecSplit (Vector.map (opD op) v)
    | ternary, unary => fun opD op v => vecSplit2 (Vector.map (opD op) v)

    | unary, binary   => fun opD op v => Vector.map2 (opD op) v
    | binary, binary  => fun opD op v1 v2 => vecSplit (Vector.map2 (opD op) v1 v2)
    | ternary, binary => fun opD op v1 v2 => vecSplit2 (Vector.map2 (opD op) v1 v2)

    | unary, ternary   => fun opD op v1 v2 v3 => Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3
    | binary, ternary  => fun opD op v1 v2 v3 => vecSplit (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3)
    | ternary, ternary => fun opD op v1 v2 v3 => vecSplit2 (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3)
    end.

  Fixpoint opDenote {la ra : arity}{k : kind}(t : type k) : op la ra -> ArityDenote la ra (T.typeDenote t) :=
    match t as t0 return op la ra -> ArityDenote la ra (T.typeDenote t0) with
    | word n => O.wordOpDenote n
    | multiword m n   => liftOpDenote (2 ^ m) (T.typeDenote (word n)) (O.wordOpDenote n)
    | array _ n _ tw    => liftOpDenote n (T.typeDenote tw) (opDenote tw)
    end.

End OpDenote.

(** We now define the semantics of the operator in the standard interpretation *)
Module StandardWordOps : OP_SEMANTICS (StandardWord).
  Import Verse.Word.
  Definition wordOpDenote la ra n (o : op la ra) :=
    let N_eucl (q r : N) := ((q / r)%N, N.modulo q r) in
    match o in op la0 ra0 return ArityDenote la0 ra0 (StandardWord.wordDenote n) with
    | plus         => Word.numBinOp N.add
    | minus        => Word.numBinOp N.sub
    | mul          => Word.numBinOp N.mul
    | exmul        => Word.numOverflowBinop N.mul
    | quot         => Word.numBinOp N.div
    | eucl         => Word.numBigargExop N_eucl
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
