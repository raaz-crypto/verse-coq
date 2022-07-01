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

(** A rewrite with a mod equation *)
Ltac modrewrite H := unfold eqMod; rewrite H; trivial.

(** As with all reflection based tactics, we have an AST to
    reify actual expressions. It consists of addition, multiplication
    and modulo computation. The expression type is parametrised by the
    modulo under which the equality is to be prove.
*)
Inductive Exp : N -> Type :=
| Const : forall M, N -> Exp M
| Add : forall M, Exp M -> Exp M -> Exp M
| Mul : forall M, Exp M -> Exp M -> Exp M
| Mod : forall M, Exp M -> Exp M.

Arguments Const {M}.
Arguments Add {M}.
Arguments Mul {M}.
Arguments Mod {M}.

Infix "+"    := Add : exp_scope.
Infix "*"    := Mul : exp_scope.

(** The evaluation function which gives the semantic meaning of the
    ast object.  *)


Fixpoint eval {M}(e : Exp M) : N :=
  match e with
  | Const x => x
  | Add e1 e2 => eval e1 + eval e2
  | Mul e1 e2 => eval e1 * eval e2
  | Mod ep    => eval ep mod M
  end.

(** The associated Ltac function that reify the expression into an exp function *)
Ltac reify e M :=
  match e with
  | (?e1 + ?e2)%N => let e1p := reify constr:(e1) M in
                    let e2p := reify constr:(e2) M in
                    constr:(Add (M:=M) e1p e2p)
  | (?e1 * ?e2)%N => let e1p := reify constr:(e1) M in
                    let e2p := reify constr:(e2) M in
                constr:(Mul (M:=M) e1p e2p)
  | (?ep mod ?M)%N => let epp := reify ep M in
                 constr:(Mod (M:=M) epp)

  | _  => constr:(Const (M:=M) e)

  end.

(** This tactic rewrites a given expression into an equivalent expression. In otherwords
it generates an assertion of the kind X = eval eX  where eX is an appropriate expression
involving the

*)
(* Ltac semantic_assertion H X eX M := assert (H: X = eval eX) by (simpl; trivial). *)
Ltac semantic_rewrite X eX
  := let H := fresh "HSem" in
     assert (H: X = eval eX) by (simpl; trivial);
     rewrite H.

(* begin hide *)
#[local] Hint Resolve
  N.mod_mod
  N.add_mod
  N.mul_mod
  : localdb.

#[local] Tactic Notation "ReW" constr(X) := (rewrite X; trivial).
#[local] Tactic Notation "ReW" "<-" constr(X) := (rewrite <- X; trivial).
(* end hide *)

(** * Normal forms.

When trying to prove modular equation of the kind X ≡ Y [mod M] the
common strategy is to first get X and Y into some sort of a normal
form. The proof then follows either directly or largely based on
either ring tactics or rewrites with modular equality hypothesis that
we have as premise. The normal forms that we need in both these cases
differ and we give two names

1. A _ring normal form_ where X (and Y) are converted to expressions
   which do not involve the mod operator. (i.e X and Y are pure
   arithmetic expression.

2. The _leaf normal form_ where all the leafs (Const). We can the
   use the premises of the kind Xᵢ ≡ Yᵢ [mod M] to do the rewrites.

*)


(** ** The ring nomal form

Getting to this form is easy. We write a function that will just wipe out
all the mod operators.

 *)


Fixpoint unmod {M}(e : Exp M) : Exp M :=
  match e with
  | Const x   => Const x
  | Add e1 e2 => let e1p := unmod e1 in
                let e2p := unmod e2 in
                Add e1p e2p
  | Mul e1 e2 => let e1p := unmod e1 in
                let e2p := unmod e2 in
                Mul e1p e2p
  | Mod ep => unmod ep
  end.

(** Its correctness follows from the following lemma *)

Lemma unmod_spec M : M <> 0%N -> forall e : Exp M, eval e ≡ eval (unmod e) [mod M].
Proof.
  intro HmNz.
  intro e.
  unfold eqMod.
  induction e as [ |M e1 IH1 e2 IH2|M e1 IH1 e2 IH2| M e IH ]; simpl.
  - trivial.
  - ReW N.add_mod; ReW IH1; ReW IH2; ReW <- N.add_mod.
  - ReW N.mul_mod; ReW IH1; ReW IH2; ReW <- N.mul_mod.
  - ReW IH; ReW N.mod_mod.
Qed.

(** The [ringnf] tactic converts the given term to is ring normal form *)

Ltac ringnf_rewrite eX M :=
  let H := fresh "HNormalise" in
  assert (H : M <> 0%N -> eval (M:=M) eX ≡ eval (M:=M) (unmod eX) [mod M])
    by (intro HmNz; apply unmod_spec; trivial);
  modrewrite H; simpl.

Ltac ringnf X M :=
  let eX := reify X M in
  semantic_rewrite X eX;
  ringnf_rewrite eX M.



Ltac ringmod := match goal with
                | [ |- ?X ≡ ?Y [mod ?M] ] =>
                    ringnf X M; ringnf Y M;
                    apply (f_equal (fun y => N.modulo y M)); ring
                end.

Goal forall x M, M <> 0%N -> ((x mod M) ≡ x [mod M])%N.
  intros x M H.
  ringmod.
Qed.
Goal forall x y z M : N, M <> 0%N -> ((x mod M + (y + z) mod M) ≡ (x + y + z) [mod M])%N.
  intros x y z M H.
  ringmod.
Qed.
