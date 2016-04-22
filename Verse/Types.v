Require Import Verse.Tactics.

(** * Types in verse.

The assembly language supported by verse is typed. We have the word
type, array types and the type of sequences.

** Words.

The type [word n] denotes [n] byte long words. Word types are also
called scalars. They are also bounded in the sense that the memory
used is fixed at compilation time.

** Arrays.

Arrays are abstractions to contiguous memory locations in the machine
each of which can store a scalar.  Therefore, modification to the
contents of an array in a function changes the contents
globally. Arrays also required to specify the endianness of the values
as it matters when loading or storing into memory.

The dimensions of the arrays are fixed at compile time. Hence, they too
are bounded.

** Sequences.

Cryptographic primitives like block cipher often process a stream of
blocks or values. A sequence abstracts this. The stream type is
unbounded and its length is not known at compile time. As a result,
verse does not allow nested streams.

*)

Inductive typeS : Type :=
| word       : nat  -> typeS   (** word n is words of 2^n bytes *)
| array      : nat  -> endian -> typeS -> typeS
| sequence   : typeS -> typeS

with endian : Type := bigE | littleE | hostE.


(** Property asserting that a type is a scalar   *)

Definition isValue (t : typeS) : Prop := exists (n : nat), t = word n.

Definition isArrayOf (t s : typeS) : Prop :=
  exists (n : nat)(e : endian), t = array n e s.

Definition isBounded (t : typeS) : Prop
  := isValue t \/ exists (n : nat)(e : endian)(s : typeS),
                    isValue s /\ t = array n e s.


(** Property that asserts that a type is well formed *)
Definition isWellformed (t : typeS) : Prop
  := isBounded t \/ exists (s : typeS), t = sequence s /\ isBounded s.

Definition type := { t : typeS | isWellformed t }.

(** * Type tactics.

Proving properties of types can get tedious. Here are some tactics
to automate these.

 *)


Module Tactics.

  (* Handle value assertions *)
  Ltac value :=
    repeat dispose;
    match goal with
      | [ |- isValue (word ?N)              ]
        => exists N; trivial
      | [ |- isValue (array _ _ _ _)        ]
        => fail 1 "array is not a value type"
      | [ |- isValue (sequence _)           ]
        => fail 1 "sequence not a value type"
      | [ |- isValue ?T                     ]
        => try (unfold T); value
    end.

  Ltac bounded :=
    repeat dispose;
    match goal with
      | [ |- isBounded (word  _) ]
        => apply or_introl; value
      | [ |- isBounded (array ?n ?e ?s) ]
        => let H := fresh "HypVal" in
           assert (H:isValue s) by value;
             apply or_intror;
             exists n;
             exists e;
             exists s; exact (H,eq_refl)
      | [ |- isBounded (sequence _) ]
        => fail 1 "sequence is not a bounded type"
      (* From stronger assumptions *)
      | [ H : isValue ?T   |- isBounded ?T  ]
        => apply or_introl; exact H
      | [ |- isBounded ?T ] => try (unfold T); bounded
    end.

  Ltac wellformed :=
    repeat dispose;
    match goal with
      | [ |- isWellformed (word _) ]
        => apply or_introl; bounded
      | [ |- isWellformed (array _ _ _ _) ]
        => apply or_introl; bounded
      | [ |- isWellformed (sequence ?T)]
        => let H := fresh "HypVal" in
           assert (H:isBounded T) by bounded;
             apply or_intror;
             exists T;
             exact (H,eq_refl)
      (* From stronger assumptions *)
      | [ _ : isValue   ?T |- isWellformed ?T ]
        => apply or_introl; bounded
      | [ H : isBounded ?T |- isWellformed ?T ]
        => apply or_introl; exact H
      (* Try unfolding and continue *)
      | [ |- isWellformed ?T ] => try (unfold T); wellformed
    end.

  (** Make a word type. The proof obligations are automatically
   handled.
   *)
  Ltac mkWord n
    := exists (word n)
              ; assert (isWellformed (word n)) by wellformed
              ; trivial.



End Tactics.
Import Tactics.

(** Some common word types *)

Definition Byte   : type.
  mkWord 1.
Qed.

Definition Word16 : type.
  mkWord 2.
Qed.

Definition Word32 : type.
  mkWord 4.
Qed.
