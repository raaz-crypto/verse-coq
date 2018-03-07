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

Local Definition LArityDenote a t : Type  := match a with
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

Definition opArityDenote (Error : Prop) larity rarity (t : Type) :=
  let dest := LArityDenote larity t in
  match rarity with
  | unary   => t -> dest + {Error}
  | binary  => t -> t -> dest + {Error}
  | ternary => t -> t -> t -> dest + {Error}
  end.

Module Type OP_SEMANTICS (W : WORD_SEMANTICS).
  Parameter OpError : Prop.
  Parameter wordOpDenote    : forall la ra n, op la ra -> opArityDenote OpError la ra (W.wordDenote n).
End OP_SEMANTICS.

Module Type NoOP_SEMANTICS (W : WORD_SEMANTICS).
  Parameter wordOpDenote    : forall la ra n, op la ra -> ArityDenote la ra (W.wordDenote n).
End NoOP_SEMANTICS.

Inductive NoOpError := NoError.
Module LiftOpSemantics (W : WORD_SEMANTICS) (O : NoOP_SEMANTICS W) <: OP_SEMANTICS W.

  Definition OpError := NoOpError.
  Definition wordOpDenote la ra n (o : op la ra) :=
    (match ra return @ArityDenote la ra _ -> @opArityDenote OpError la ra _ with
    | unary => fun oD => compose inleft oD
    | binary => fun oD => compose (compose inleft) oD
    | ternary => fun oD => compose (compose (compose inleft)) oD
     end) (O.wordOpDenote n o).

End LiftOpSemantics.

Module OpDenote (W : WORD_SEMANTICS)(O : OP_SEMANTICS W).

  Import O.
  Module T := TypeDenote W.

  Local Fixpoint liftErr Err T m (v : Vector.t (T + {Err}) m) : Vector.t T m + {Err} :=
    match v with
    | Vector.nil _ => {- Vector.nil _ -}
    | Vector.cons _ t _ vt => t' <- t; Vector.cons _ t' _ <$> (liftErr vt)
    end.

  Local Definition opVecSplit Err T1 T2 m (v : Vector.t (T1 * T2 + {Err}) m) :=
    pair <$> liftErr (Vector.map (ap fst) v) <*>  liftErr (Vector.map (ap snd) v).

  Local Definition opVecSplit2 Err T1 T2 T3 m (v : Vector.t (T1 * T2 * T3 + {Err}) m) :=
    pair <$> opVecSplit (Vector.map (ap fst) v) <*> liftErr (Vector.map (ap snd) v).

  Local Definition vecApply T1 T2 m (v : Vector.t (T1 -> T2) m) := Vector.map2 apply v.

  Local Definition liftOpDenote m typ la ra : (op la ra -> opArityDenote OpError la ra typ) ->
                                              op la ra -> opArityDenote OpError la ra (Vector.t typ m) :=
    match la, ra return (op la ra -> opArityDenote OpError la ra typ) ->
                        op la ra ->
                        opArityDenote OpError la ra (Vector.t typ m)
    with
    | unary, unary   => fun opD op v => liftErr (Vector.map (opD op) v)
    | binary, unary  => fun opD op v =>  (opVecSplit (Vector.map (opD op) v))
    | ternary, unary => fun opD op v => (opVecSplit2 (Vector.map (opD op) v))
    | unary, binary   => fun opD op v1 v2 => liftErr (Vector.map2 (opD op) v1 v2)
    | binary, binary  => fun opD op v1 v2 => (opVecSplit (Vector.map2 (opD op) v1 v2))
    | ternary, binary => fun opD op v1 v2 => (opVecSplit2 (Vector.map2 (opD op) v1 v2))
    | unary, ternary   => fun opD op v1 v2 v3 => liftErr (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3)
    | binary, ternary  => fun opD op v1 v2 v3 =>  (opVecSplit (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3))
    | ternary, ternary => fun opD op v1 v2 v3 =>  (opVecSplit2 (Vector.map2 apply (Vector.map2 (opD op) v1 v2) v3))
    end.

  Fixpoint opDenote {la ra : arity}{k : kind}(t : type k) : op la ra -> opArityDenote OpError la ra (T.typeDenote t) :=
    match t as t0 return op la ra -> opArityDenote OpError la ra (T.typeDenote t0) with
    | word n => wordOpDenote n
    | multiword m n   => liftOpDenote (2 ^ m) (T.typeDenote (word n)) (O.wordOpDenote n)
    | array _ n _ tw    => liftOpDenote n (T.typeDenote tw) (opDenote tw)
    end.

End OpDenote.

(** We now define the semantics of the operator in the standard interpretation *)
Module StandardWordOps : NoOP_SEMANTICS (StandardWord).
  Import Verse.Word.
  Definition wordOpDenote la ra n (o : op la ra) :=
    match o in op la0 ra0 return ArityDenote la0 ra0 (StandardWord.wordDenote n) with
    | plus         => Word.numBinOp N.add
    | minus        => Word.numBinOp N.sub
    | mul          => Word.numBinOp N.mul
    | exmul        => Word.numOverflowBinop N.mul
    | quot         => Word.numBinOp N.div
    | eucl         => Word.numBigargExop N.div_eucl
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

Module StandardOpSemantics := LiftOpSemantics StandardWord StandardWordOps.
(** And here is the standard meaning of operations lifted to the type world *)
Module StandardOps := OpDenote StandardWord StandardOpSemantics.
