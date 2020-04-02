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

Inductive extension := DataKinds | ForeignFunctionInterface.

Inductive line :=
| language  : extension -> line
| module    : forall N, N    -> line
| import    : forall N, N    -> line
| ccall     : forall N, N    -> Args -> line.

Inductive RaazMods := RaazCore.

Notation "'Raaz.Core'" := RaazCore (only printing).


Arguments module [N].
Arguments import [N].
Arguments ccall [N].

Inductive Program := program : list line -> Program.

Require List.
Import List.ListNotations.

Definition mkProgram {Name} (modName : Name)(lns : list line) : Program
  := program ( [ language DataKinds;
                 language ForeignFunctionInterface;
                 module modName;
                 import RaazCore
               ]
                 ++ lns)%list.

Arguments mkProgram [Name].

Notation "{-#  'LANGUAGE'  X  #-}" := (language X) (only printing).
Notation "'module' N 'where'"   := (module N) (only printing).
Notation "'import' N"           := (import N) (only printing, at level 1).
Notation "'foreign' 'import' 'ccall' 'unsafe' N A"
  := (ccall N A)
       ( only printing,
         format "'foreign'  '[hv' 'import'  'ccall'  'unsafe'  N '//' A ']'",
         at level 2).


Notation "X .. Y" := (program (cons X .. (cons Y nil) ..))
         ( only printing,
           format "X '//' .. '//' Y",
           at level 0
         ).
