(*  * Core type associated with Verse.



*)

(** * Operators of Verse language.

We begin defining expressions by defining operators for the expression
language.  Most architectures allow various basic arithmetic and
bitwise operations on values stored in the registers. These operations
are captured by the type [op] which is parameterised by the arity of
the operation.

 *)

Inductive op : nat -> Set :=
| plus    : op 2
| minus   : op 2
| mul     : op 2
| quot    : op 2
| rem     : op 2
| bitOr   : op 2
| bitAnd  : op 2
| bitXor  : op 2
| bitComp : op 1
| rotL    : nat -> op 1
| rotR    : nat -> op 1
| shiftL  : nat -> op 1
| shiftR  : nat -> op 1
.

(** * Endian

 Type that captures endian of a machine.

 *)

Inductive endian : Set := bigE | littleE | hostE.
