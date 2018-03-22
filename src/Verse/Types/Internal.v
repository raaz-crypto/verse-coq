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

Class typeC (t : Type) := { mkWord      : nat -> t;
                            mkMultiword : nat -> nat  -> t;
                            mkArray     : nat -> endian -> t -> t
                          }.

(**

Final representations can be seen as giving certain semantics for
types, in the sense that it gives meaning for each type. We use denote
to get this meaning.

 *)

Fixpoint typeDenote {t : Type}{tc : typeC t} {k} (ty : type k)  :  t  :=
    match ty with
    | word n        => mkWord n
    | multiword m n => mkMultiword m n
    | array n e t   => mkArray n e (typeDenote t)
    end.



(** ** Sematics of [type]'s as a final representation.

A special case of final representation is to encode types as Coq
types. All we need in this case is a representation of
words. Multi-words [multiword m n] are then defined as a vectors of
these word type, and finally arrays are vectors over the element
type. To support maximum flexibility, meaning of types are
parameterised by the definition of the word.

*)


Definition mkTypeDenote (wordDenote : nat -> Type) : typeC Type
  := {| mkWord := wordDenote;
        mkMultiword := fun m n => Vector.t (wordDenote n)  (2 ^ m);
        mkArray     := fun n _ t => Vector.t t n
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

Definition StandardSemantics : typeC Type := mkTypeDenote stdWordDenote.

Import Verse.PrettyPrint.
Global Instance word_constant_pretty n : PrettyPrint (stdWordDenote n) := word_pretty (8 * 2^n).
