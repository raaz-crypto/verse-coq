Require Import NArith.


(* * Types with bounds.

Consider a type together with a measure (which is a function form A to
N). This type captures values with a bound on their measure.

 *)

Inductive Bounded A (mu : A -> N) :=
| bounded : forall (a : A)(n : N), (mu a <= n)%N -> Bounded A mu.

Arguments bounded {A mu}.

(** There is a natural injection of A into its bounded counterpart *)
Definition injB {A mu}(a : A) : Bounded A mu :=
  bounded a (mu a) (N.le_refl (mu a)).

(** Forget the bound *)
Definition forget {A mu}(ba : Bounded A mu) : A :=
  match ba with
  | bounded a _ _ => a
  end.

(** Get the bound on the value *)

Definition boundOf {A mu}(ba : Bounded A mu) : N :=
  match ba with
  | bounded _ n _ => n
  end.

(** Get the bound proof *)
Definition boundProof {A mu}(ba : Bounded A mu) : (mu (forget ba) <= boundOf ba)%N
  := match ba with
     | bounded _ _ pf => pf
     end.

(** ** Bounded binary Naturals

This is just Bound N mu where mu is the identity function.

*)

Definition BN := Bounded N (fun x : N => x).

(**  There is a natural function from any bounded type to BN *)
Definition toBN {A toN} (ba : Bounded A toN) : BN :=
  bounded (toN (forget ba)) (boundOf ba)(boundProof ba).


Require Import NFacts.
Require Import setoid_ring.Algebra_syntax.


#[export] Instance zero_BN : Zero BN := injB 0%N.
#[export] Instance one_BN : One BN := injB 1%N.

#[export] Program Instance add_BN : Addition BN :=
  fun x y => match x, y with
          | bounded a n pfx, bounded b m pfy => bounded (a+b)%N (n+m)%N _
          end.

Next Obligation.
  eauto with Nfacts.
Qed.

#[export] Program Instance mul_BN : @Multiplication BN BN :=
  fun x y => match x, y with
          | bounded a n pfx, bounded b m pfy => bounded (a*b)%N (n*m)%N _
          end%N.

Next Obligation.
  eauto with Nfacts.
Qed.

#[export] Instance zero_N : Zero N := 0%N.
#[export] Instance one_N  : One N := 1%N.
#[export] Instance add_N  : Addition N := N.add.
#[export] Instance mul_N  : Multiplication := N.mul.
