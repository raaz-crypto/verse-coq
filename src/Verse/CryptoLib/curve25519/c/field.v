(* begin hide *)
Require Import Arith.
Require Import Verse.
(* end hide *)
(** * Field arithmetic over GF(2²⁵⁵ - 19).


In this module, we implement the field arithmetic over the base field
𝔽 = GF(2²⁵⁵ - 19). we start with considering the representation of
elements of this field.


 *)


(** ** Representing elements.


There are two possible representations of elements in this field

* The packed representation as a 255 bit little endian quantity
  represented as 32 bytes. We consider this as 4 -64-bit little endian
  values.

* The computational representation: Consider the 255 bit number in
  base 2⁵¹ as α = x₀ + x₁ 2⁵¹ .... + x₅ 2²⁰⁴. Each of the xᵢ's
  themselves can be considered as aᵢ + bᵢ 2²⁶.



The packed representation is the standard representation and is in
particular used to storing and transmitting values of the latter and
is thus canonical.  The computational representation should be treated
as an implementation dependent internal format and is designed to make
the implementation of the field operation efficient.

 *)

Definition pow2 (i : nat) :=
  let j := i / 2 in
  let k := i mod 2 in
  j * 51 + k * 26.


(** The bit range that goes into the ith limb vᵢ and the number of bits that it should hold. *)

Definition bitrange (i : nat) := (pow2 i, pow2 (i + 1) ).
Definition nbits   (i : nat) := let (l,h) := bitrange i in
                              h - l.

Definition bitSizes := iterate (fun i (_ : i < 10) =>[nbits i]).


(* begin hide *)
(* NOTE: These are inline tests *)

(* Make sure that all the 255 bits are distributed some where.
Goal List.fold_left Nat.add bitSizes 0 = 255.
  trivial.
Qed.

(* end hide *)
