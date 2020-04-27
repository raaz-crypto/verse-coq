Require Import Verse.BitVector.
Require Import BinNat.
Require Import Arith.
Require Import NArith.


Require Import Verse.Ast.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.

Module Internals.

  Definition selL (ty : type direct) n : const ty
    := let mask sz : const (word sz) := lower_ones (bitSize sz) n in
       match ty with
       | word sz         => mask sz
       | multiword m sz  => Vector.const (mask sz) (2^m)
       end.

  Definition selU (ty : type direct) n : const ty
    := let mask sz : const (word sz) := upper_ones (bitSize sz) n in
       match ty with
       | word sz         => mask sz
       | multiword m sz  => Vector.const (mask sz) (2^m)
       end.


  Definition clearL (ty : type direct) n : const ty
    := let mask sz : const (word sz) :=
           let bsz := bitSize sz in upper_ones bsz (bsz - n)
       in
       match ty with
       | word sz         => mask sz
       | multiword m sz  => Vector.const (mask sz) (2^m)
       end.


  Definition clearU (ty : type direct) n : const ty
    := let mask sz : const (word sz) :=
           let bsz := bitSize sz in lower_ones bsz (bsz - n)
       in
       match ty with
       | word sz         => mask sz
       | multiword m sz  => Vector.const (mask sz) (2^m)
       end.

  Definition selShiftR (ty : type direct) n : nat
    := match ty with
       | word sz => bitSize sz - n
       | multiword _ sz => bitSize sz - n
       end.
End Internals.

(**  Expression that selects the n most significant bits of a constant *)



Require Import Verse.Language.Pretty.

(** * Select or clear bits

The [selectLower n] ([selectUpper n]) selects the lower (respectively
upper) bits of the given constant expression.  Similarly [clearLower
n] ([clearUpper n]) clears the lower (respectively upper) bits.  If
the expression is of type multiword, then the select/clear functions
selects or clears n bits from each of the component of the multiword.

*)

Definition selectLower (n : nat) {v : VariableT}{ty : type direct }{E}{inst : EXPR v ty E} (e: E)
  := e AND (Internals.selL ty n).

Definition selectUpper (n : nat) {v : VariableT}{ty : type direct }{E}{inst : EXPR v ty E} (e: E)
  := e AND (Internals.selU ty n).

Definition clearLower (n : nat) {v : VariableT}{ty : type direct }{E}{inst : EXPR v ty E} (e: E)
  := e AND (Internals.clearL ty n).

Definition clearUpper (n : nat) {v : VariableT}{ty : type direct }{E}{inst : EXPR v ty E} (e: E)
  := e AND (Internals.clearU ty n).

(**
    This function selects the upper [n] bits and then shifts the lower n-m bits out. As numbers
    this corresponds to taking remainder with

*)
Definition selectAndShiftR  (n : nat) {v : VariableT}{ty : type direct }{E}{inst : EXPR v ty E} (e: E)
  := e >> (Internals.selShiftR ty n).

Definition selectShiftRAndUpdate  (n : nat)
           {v : VariableT}{ty : type direct }{L}{inst : LEXPR v ty L} (l: L)
  := l ::=>> (Internals.selShiftR ty n).
