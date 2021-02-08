(* A monad to alloc and free variables *)

Require Import Verse.Monad.


Inductive Alloc v A :=
| aret : A -> list v -> Alloc v A
| alloc : (v -> Alloc v A) -> Alloc v A.

Arguments aret  {v A}.
Arguments alloc {v A}.
Require Import List.
Import ListNotations.
Check aret.



Fixpoint use {v A} (x : v) (ma : Alloc v A) : Alloc v A
  := match ma with
     | aret a ys => aret a (x :: ys)
     | alloc f   => f x
     end.

Definition reuse {v A}  : Alloc v A -> list v -> Alloc v A
  := List.fold_right (fun x action => use x action).

Lemma use_ret_cons {v A} : forall (x : v) l (a : A), use x (aret a l) = aret a (x :: l).
  intros.
  trivial.
Qed.

Lemma reuse_ret_app {v A} : forall (l0 l1 : list v) (a : A), reuse  (aret a l1) l0 = aret a (l0 ++ l1).
  intros.
  induction l0; simpl; trivial.
  rewrite <- use_ret_cons.
  rewrite IHl0; trivial.
Qed.

Definition apure v T : T -> Alloc v T :=
  fun t => aret t []%list.


Fixpoint abind {v A B} (ma : Alloc v A) (fmb : A -> Alloc v B) : Alloc v B
  := match ma with
     | aret t fv => reuse (fmb t) fv
     | alloc f   => alloc (fun v => abind (f v) fmb)
     end.

Instance alloc_monad v : Monad (Alloc v) := { pure := @apure v  ; bind := @abind v }.

Lemma alloc_pure_id_l : forall v, pure_id_l (alloc_monad v).
  crush_monad_laws.
Qed.


Require Import FunctionalExtensionality.
Lemma alloc_pure_id_r : forall v, pure_id_r (alloc_monad v).
  unfold pure_id_r.
  intros; simpl; unfold apure.
  induction ma; simpl.
  - rewrite reuse_ret_app; rewrite app_nil_r; trivial.
  - f_equal. apply functional_extensionality; assumption.
Qed.

Lemma abind_use {v A B} : forall (x : v)(ma : Alloc v A)(g : A -> Alloc v B), abind (use x ma) g = use x (abind ma g).
  intros.
  induction ma; simpl; apply f_equal; trivial.
Qed.

Lemma alloc_bind_assoc : forall v, bind_assoc (alloc_monad v).
  intros.
  unfold bind_assoc.
  intros.
  simpl.
  induction ta; simpl; try (f_equal; apply functional_extensionality; assumption).
  induction l; trivial;
    simpl. rewrite <- IHl.
  apply abind_use.
Qed.

Lemma alloc_monad_laws : forall v, monad_laws (alloc_monad v).
  intro.
  repeat constructor.
  apply alloc_pure_id_r.
  apply alloc_bind_assoc.
Qed.
