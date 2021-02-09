Require List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Arith.

Require Import BinNat.

Definition term A          := (A * nat)%type.
Definition poly (A : Type) := list (term A).

(* Evaluation of polymomial at a value *)

Definition evalT (eta : nat) (tm : term nat) : nat:=
  let (coef, p) := tm in coef * eta ^ p.

Definition eval eta (p : poly nat) : nat :=
  let fldr (tm : term nat) sum := (sum + evalT eta tm)
  in List.fold_right fldr 0 p.


Definition add {A : Type}(p1 p2 : poly A) := p1 ++ p2.

Definition mulTT (t1 t2 : term nat) : term nat :=
  let (coef1, p1) := t1 in
  let (coef2, p2) := t2 in
  (coef1 * coef2 , p1 + p2).

Definition mulTP (t : term nat) : poly nat -> poly nat :=
  List.map (mulTT t).

Fixpoint mul (p1 p2 : poly nat) : poly nat :=
  match p1 with
  | [] => []
  | (t :: ts) => add (mulTP t p2)  (mul ts p2)
  end.


Section Spec.
  Context {eta : nat}.


  Lemma add_spec : forall p1 p2, eval eta p1 + eval eta p2 = eval eta (add p1 p2).
  Proof.
    intros.
    induction p1; simpl; trivial.
    rewrite <- IHp1.
    ring.
  Qed.

  Lemma mulTT_spec : forall t1 t2, evalT eta (mulTT t1 t2) = evalT eta t1 * evalT eta t2.
    intros; destruct t1; destruct t2; simpl.
    rewrite Nat.pow_add_r; ring.
  Qed.

  Lemma mulTP_spec : forall tm p, eval eta (mulTP tm p) = evalT eta tm * eval eta p.
    intros.
    induction p; simpl; trivial.
    rewrite IHp.
    rewrite (mulTT_spec).
    ring.
  Qed.

  Lemma mul_spec : forall p1 p2, eval eta (mul p1 p2) = eval eta p1 * eval eta p2.
    intros.
    induction p1; simpl; trivial.
    ring_simplify.
    rewrite <- IHp1.
    rewrite <- mulTP_spec.
    rewrite <- add_spec.
    ring.
  Qed.
End Spec.
