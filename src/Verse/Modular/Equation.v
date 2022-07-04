(* begin hide *)
Require Import ZArith.
Require Import NArith.
Require  List.
Import List.ListNotations.


Create HintDb localdb.
Local Declare Scope exp_scope.
Local Delimit Scope exp_scope with exp.

(* end hide *)

(** * Simple modular arithmetic proofs.

This module implements a reflection based proving for identities of
the kind X ≡ Y mod M.

 *)

Definition eqMod (X Y M : N) : Prop := (X mod M = Y mod M)%N.
Notation "X ≡ Y [mod M ]"  := (eqMod X Y M) (at level 70).

Ltac modring M := apply (f_equal (fun y => N.modulo y M)); ring.

(*

- Rewriting using equations of the kind A ≡ B [mod M]. We give a tactic
  to rewrite with equations of the kind A ≡ B [mod M].

 *)

Ltac modrewrite H := unfold eqMod; rewrite H; trivial.
Ltac automodrewrite := repeat match goal with
                         | [ H : _ ≡ _ [mod ?M] |- _ ] => modrewrite H; trivial
                         end.
