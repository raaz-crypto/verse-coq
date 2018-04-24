Require Import Verse.Error.
Require Import Verse.Word.
Require Import Arith.
Import Nat.

(** printing power2m   $ 2^m     $ # 2<sup> m   </sup> # *)
(** printing power2n   $ 2^n     $ # 2<sup> n   </sup> # *)
(** printing power2p3  $ 2^3     $ # 2<sup> 3   </sup> # *)
(** printing power2np3 $ 2^{n+3} $ # 2<sup> n+3 </sup> # *)


(** * Types in its full glory.

The Verse EDSL is a typed machine language consisting of [word]s,
[multiword]s, and [array]s of which the first two, i.e. [word]s and
[multiword]s, can reside in the registers of the machine where as
[array]s are necessarily stored in the machine memory. The kind system
indicates this distinction in type.

*)

Inductive kind   : Type := direct | memory.
Inductive endian : Type := bigE | littleE | hostE.


Inductive type       : kind -> Type :=
| word               : nat -> type direct
| multiword          : nat -> nat    -> type direct
| array              : nat -> endian -> type direct -> type memory
.


(** Compute the size of a type in bytes. *)
Fixpoint sizeOf {k} (ty : type k) :=
  match ty with
  | word n         => 2 ^ n
  | multiword m n  => 2 ^ m * 2 ^ n
  | array n _ tw => n * sizeOf tw
  end.


(** Often we need to existentially quantify over types and other
    objects. This definition is just for better readability.
 *)

Definition some {P: Type} (A : P -> Type) := sigT A.


(** * Final representation.

The data types give the initial representation of verse types. It is
often easier to work with a final representation of types particularly
when we want to define semantics, pretty printing etc. The type class
below provides the mechanism for this.

 *)

Class typeC (t : kind -> Type) := { mkWord      : nat -> t direct ;
                                   mkMultiword : nat -> nat  -> t direct ;
                                   mkArray     : nat -> endian -> t direct -> t memory
                                 }.

(**

Final representations can be seen as giving certain semantics for
types, in the sense that it gives meaning for each type. The parameter
[t : kind -> Type] is the domain of interpretation of types. The
following function can now be seen as the translation from types of
verse into the domain of interpretation which is [t].

 *)

Fixpoint typeDenote {t : kind -> Type}{tc : typeC t} {k} (ty : type k)  :  t k  :=
    match ty with
    | word n        => mkWord n
    | multiword m n => mkMultiword m n
    | array n e t   => mkArray n e (typeDenote t)
    end.



(** ** Sematics of [type]'s as a final representation.

A special case of final representation is to encode types as Coq
types. In this case the All we need in this case is a representation of
words. Multi-words [multiword m n] are then defined as a vectors of
these word type, and finally arrays are vectors over the element
type. To support maximum flexibility, meaning of types are
parameterised by the definition of the word.

*)

Definition TypeDenote := fun _ : kind => Type.

Definition mkTypeDenote (wordDenote : nat -> Type) : typeC TypeDenote
    := {| mkWord := fun n => wordDenote n;
          mkMultiword :=  fun m n => Vector.t (wordDenote n)  (2 ^ m);
          mkArray     :=   fun n _ (t : Type) => Vector.t t n
       |}.

(** *** The standard word semantics.

The standard semantics is were [word n] means unsigned integers of
[power2n] bytes. We refrain for defining an instance declaration here
because there are other word semantics that are equally useful for us.
It is expected that one declares a local instance as the application
demands.

*)

Require Import Verse.Word.
Definition stdWordDenote : nat -> Type := fun n => Word.bytes (2^n).

Definition StandardSemantics : typeC TypeDenote := mkTypeDenote stdWordDenote.

Import Verse.PrettyPrint.
Global Instance word_constant_pretty n : PrettyPrint (stdWordDenote n) := word_pretty (8 * 2^n).
