(* begin hide *)
Require Import ZArith.
Require Import NArith.
Require  List.
Import List.ListNotations.
Require Import Verse.Modular.Equation.

Create HintDb localdb.
Local Declare Scope exp_scope.
Local Delimit Scope exp_scope with exp.

(* end hide *)

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
form. The proof then follows either directly or largely based on one
of the two cases.

- Essentially the ring tactics on the underlying ring N. The [modring]
  tactic is given for this purpose which disposes of equation of the
  kind X ≡ Y [mod M] by essentially proving the stronger claim X = Y
  using the ring tactic on N

*)

(*

- Rewriting using equations of the kind A ≡ B [mod M]. We give a tactic
  to rewrite with equations of the kind A ≡ B [mod M].

 *)

(** * Generalised normalisation.

A generalised normalisation is by a normalisation function and
its correctness theorem.

 *)

Record normalisation := { nf :> forall M, Exp M -> Exp M;
                          nf_spec : forall M (e : Exp M), M <>0%N -> eval e ≡ eval (nf M e) [mod M]
  }.


(** We now give a reflection based normalisation of expression *)

(*
Ltac ringnf_rewrite eX M :=
  let H := fresh "HNormalise" in
  assert (H : M <> 0%N -> eval (M:=M) eX ≡ eval (M:=M) (unmod eX) [mod M])
    by (intro HmNz; apply unmod_spec; trivial);
  modrewrite H; simpl.
*)
Ltac nf_rewrite norm eX M := modrewrite (nf_spec norm M eX); simpl.

Ltac nf norm X M :=
  let eX := reify X M in
  semantic_rewrite X eX;
  nf_rewrite norm eX M.

Ltac normalise norm := match goal with
                       |  [ |- ?X ≡ ?Y [mod ?M] ]
                          =>  nf norm X M;
                             nf norm Y M; trivial
                       end.

(** ** The ring nomal form.

The ring normal for is obtained by removing any intermediate mod
operations in the equation X ≡ Y [mod N] equation.

 *)


Fixpoint unmod {M} (e : Exp M) : Exp M :=
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

(** We have the following correctness theory for the above
transformation *)

Lemma unmod_spec (M : N) : forall (e : Exp M), M <> 0%N -> eval e ≡ eval (unmod e) [mod M].
Proof.
  intro e.
  intro HmNz.
  unfold eqMod.
  induction e as [ |M e1 IH1 e2 IH2|M e1 IH1 e2 IH2| M e IH ]; simpl.
  - trivial.
  - ReW N.add_mod; ReW IH1; ReW IH2; ReW <- N.add_mod.
  - ReW N.mul_mod; ReW IH1; ReW IH2; ReW <- N.mul_mod.
  - ReW IH; ReW N.mod_mod.
Qed.

Definition RingN : normalisation := {| nf := @unmod;
                                       nf_spec := unmod_spec
                                    |}.


Ltac ringnf := nf RingN.
Ltac ringmod := normalise RingN.

(** ** The leaf normal form

In this normal form the terms in the modular equation have their mod
operations on the leaves.

*)

Fixpoint modleaf {M}(e : Exp M) : Exp M :=
  match e with
  | Const x => Mod (Const x)
  | Add e1 e2 => let e1p := modleaf e1 in
                let e2p := modleaf e2 in
                Add e1p e2p
  | Mul e1 e2 => let e1p := modleaf e1 in
                let e2p := modleaf e2 in
                Mul e1p e2p
  | Mod ep => modleaf ep
  end.

#[local] Hint Resolve N.mod_mod : localdb.
Lemma modleaf_spec M :  forall e : Exp M, M <> 0%N -> eval e ≡ eval (modleaf e) [mod M].
Proof.
  intro e.
  intro HmNz.
  induction e as [ |M e1 IH1 e2 IH2|M e1 IH1 e2 IH2| M e IH ]; simpl.
  - unfold eqMod. trivial; ReW N.mod_mod.
  - modrewrite N.add_mod; modrewrite IH1; modrewrite IH2; ReW <- N.add_mod.
  - modrewrite N.mul_mod; modrewrite IH1; modrewrite IH2. ReW <- N.mul_mod; eauto with localdb.
  - modrewrite IH; ReW N.mod_mod.
Qed.

Definition LeafN : normalisation := {| nf := @modleaf;
                                       nf_spec := modleaf_spec
                                    |}.

Ltac leafnf := nf LeafN.
Ltac leafmod := normalise LeafN.

(** ** Tactics for normalisation.

We give general tactics that can be used with both the normalisations.

*)

(**

*)
(** The [ringnf] tactic converts the given term to is ring normal form *)

Goal forall x M, M <> 0%N -> ((x mod M) ≡ x [mod M])%N.
  intros x M H.
  ringmod.
Qed.
Goal forall x y z M : N, M <> 0%N -> ((x mod M + (y + z) mod M) ≡ (x + y + z) [mod M])%N.
  intros x y z M H.
  ringmod; modring M.
Qed.

Goal forall x1 x2  y1 y2 M, M <> 0%N
                       ->  (x1 ≡ x2 [mod M])
                       ->  (y1 ≡ y2 [mod M])
                       ->  ((x1 + y1 mod M) ≡ (x2 + y2) [mod M])%N.
  intros x1 x2 y1 y2 M HmNz H1 H2.
  leafmod.
  automodrewrite.
Qed.
