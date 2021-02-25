Require List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Arith.

Require Import BinNat.

Definition term A          := (A * nat)%type.
Definition poly (A : Type) := list (term A).
Definition xpownTimes {A} (n : nat) : poly A -> poly A :=
  let mapper (tm : A * nat) := let (coef, i) := tm in (coef, i + n)
  in List.map mapper.

(**

In the rather simple representation addition is just concatenation of
the associated rings. We therefore define it for all coefficients (not
necessarily rings).

 *)
Definition add {A : Type}(p1 p2 : poly A) := p1 ++ p2.

(** Type classes for ring *)

Class Semi_Ring_Zero S := semi_ring_zero : S.
Class Semi_Ring_One  S := semi_ring_one : S.
Class Semi_Ring_Add  S := semi_ring_add : S -> S -> S.
Class Semi_Ring_Mul  S := semi_ring_mul : S -> S -> S.

(*

This is needed for proving correctness for arbitrary rings

*)
Class Semi_Ring_Eq   S := semi_ring_eq : S -> S -> Prop.

Class Semi_Ring S
      `{Semi_Ring_Zero S}
      `{Semi_Ring_One S}
      `{Semi_Ring_Add S}
      `{Semi_Ring_Mul S}
      `{Semi_Ring_Eq S}
  := {}. (* semi_ring_spec: semi_ring_theory semi_ring_zero
                                      semi_ring_one
                                      semi_ring_add
                                      semi_ring_mul
                                      semi_ring_eq. *)


Declare Scope ring_scope.
Delimit Scope ring_scope with ring.
Notation "0" := semi_ring_zero : ring_scope.
Notation "1" := semi_ring_one : ring_scope.
Infix "+" := semi_ring_add   : ring_scope.
Infix "*" := semi_ring_mul   : ring_scope.

Fixpoint pow {SR : Type}`{Semi_Ring SR}(eta : SR)(n : nat) :=
  match n with
  | 0   => 1%ring
  | S m => (eta  * (pow eta m))%ring
  end.

Infix "^" := pow :ring_scope.


Section Operations.

  Context {SR : Type}`{Semi_Ring SR}.

  (* Evaluation of polymomial at a value *)

  Definition evalT (eta : SR) (tm : term SR) : SR :=
    let (coef, p) := tm in (coef * eta ^ p)%ring.

  Definition eval eta (p : poly SR) : SR :=
    let fldr (tm : term SR) sum := (sum + evalT eta tm)%ring
    in List.fold_right fldr 0%ring p.


  Definition mulTT (t1 t2 : term SR) : term SR :=
    let (coef1, p1) := t1 in
    let (coef2, p2) := t2 in
    ((coef1 * coef2)%ring , p1 + p2).

  Definition mulTP (t : term SR) : poly SR -> poly SR :=
    List.map (mulTT t).

  Fixpoint mul (p1 p2 : poly SR) : poly SR :=
    match p1 with
    | [] => []
    | (t :: ts) => add (mulTP t p2)  (mul ts p2)
    end.

End Operations.

Instance nat_zero : Semi_Ring_Zero nat := 0.
Instance nat_one : Semi_Ring_One nat := 1.
Instance nat_add : Semi_Ring_Add nat := Nat.add.
Instance nat_mul : Semi_Ring_Mul nat := Nat.mul.
Instance nat_eq  : Semi_Ring_Eq nat  := eq.
Instance nat_semi_ring : Semi_Ring nat  := {}.

Section Spec.
  Context {eta : nat}.

  Ltac specialise_to_nat :=
    repeat (unfold semi_ring_add; unfold semi_ring_mul; unfold nat_add; unfold nat_mul).

  Ltac specialise_nat_ring:=
     specialise_to_nat; ring.

  Lemma add_spec : forall (p1 p2 : poly nat), eval eta p1 + eval eta p2 = eval eta (add p1 p2).
    intros.
    induction p1; simpl; trivial.
    rewrite <- IHp1.
    specialise_nat_ring.
  Qed.

  Lemma power_lemma : forall (x : nat)(p : nat), pow x p = x ^ p.
  Proof using Type.
    intros.
    induction p; simpl; trivial.
    rewrite <- IHp. easy.
  Qed.

  Lemma mulTT_spec : forall t1 t2, evalT eta (mulTT t1 t2) = evalT eta t1 * evalT eta t2.
    intros; destruct t1; destruct t2; simpl.
    repeat rewrite power_lemma.
    rewrite Nat.pow_add_r.
    specialise_nat_ring.
  Qed.

  Lemma mulTP_spec : forall tm p, eval eta (mulTP tm p) = evalT eta tm * eval eta p.
    intros.
    induction p; simpl; trivial.
    rewrite IHp.
    rewrite (mulTT_spec).
    specialise_nat_ring.
  Qed.

  Lemma mul_spec : forall p1 p2, eval eta (mul p1 p2) = eval eta p1 * eval eta p2.
    intros.
    induction p1; simpl; trivial.
    rewrite <- add_spec.
    rewrite mulTP_spec.
    rewrite IHp1.
    specialise_nat_ring.
  Qed.
End Spec.
