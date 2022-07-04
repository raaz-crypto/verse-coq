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


Lemma mod_eqMod : forall M x y, x ≡ y [mod M] -> (x mod M = y mod M)%N.
  trivial.
Qed.

Ltac modring M := match goal with
                  | [ |- ?X ≡ ?Y [mod ?M] ] =>
                      apply (f_equal (fun y => N.modulo y M)); ring
                  end.

(*

- Rewriting using equations of the kind A ≡ B [mod M]. We give a tactic
  to rewrite with equations of the kind A ≡ B [mod M].

 *)

Tactic Notation "modrewrite" constr(H) := unfold eqMod; rewrite H; apply mod_eqMod.
Tactic Notation "modrewrite" "<-" constr(H) := unfold eqMod; rewrite <- H; apply mod_eqMod.


Ltac automodrewrite := repeat match goal with
                         | [ H : _ ≡ _ [mod ?M] |- _ ] => modrewrite H ; trivial
                         end.

(*
Goal forall x1 x2 y1 y2 M, x1 ≡ x2 [mod M] -> y1 ≡ y2 [mod M] -> x1 mod M + y1 mod M ≡ x2 + y2 [mod M].
  intros.
  modrewrite H.
  modrewrite H0.
  modrewrite <- H.
  modrewrite <- H0.
Abort.
 *)
