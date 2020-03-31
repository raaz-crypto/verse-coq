Require Import Verse.TypeSystem.
Require Import Arith.
Inductive type : Type :=
| Word       : endian -> nat -> type
| Tuple      : nat -> type -> type
| Ptr        : type -> type
| AlignedPtr : nat -> type -> type
.

(** Helper function to set the endianness of the word involved in the type *)
Fixpoint setEndian (e : endian)(r : type) : type :=
  match r with
  | Word  _ w => Word   e w
  | Tuple n r => Tuple  n (setEndian e r)
  | Ptr     r => Ptr      (setEndian e r)
  | AlignedPtr n r => AlignedPtr n (setEndian e r)
  end.


Notation "'LE' 'Word' N" := (Word littleE N)
                              (format "'LE'  'Word' N", at level 10).
Notation "'BE' 'Word' N" := (Word bigE N)
                              (format "'BE'  'Word' N", at level 10).
Notation "'Word' N"      := (Word hostE N)
                              (format "'Word' N", at level 1).

Inductive Args :=
| args : list type -> Args.

Notation ":: X -> .. -> Y -> 'IO' ()"
  := (args (cons X .. (cons Y nil) ..))
       ( only printing, at level 1,
         format "::  X  '/' ->  ..  '/' ->  Y  '/' ->  'IO'  ()"
       ).

Notation ":: X -> 'IO' ()"
   := (args (cons X nil)) ( only printing, at level 1).

Inductive Foreign :=
| foreignC : forall N, N -> Args -> Foreign.

Definition ccall {N} (n : N) l := foreignC N n (args l).

Arguments ccall [N].

Notation "'foreign' 'import' 'ccall' 'unsafe' N A"
  := (foreignC _ N A)
       ( only printing,
         format "'foreign'  '[hv' 'import'  'ccall'  'unsafe'  N '//' A ']'",
         at level 2).
