(** * Some useful bounds N.

*)

Require Export BinNat.
Require Export NArith.
Hint Resolve N.le_refl
       N.le_le_succ_r
       N.lt_succ_diag_r
       N.lt_lt_succ_r
       N.size_gt
       N.le_trans
       N.lt_le_trans
       N.le_lt_trans
       N.le_0_l
       N.pow_nonzero
       N.pow_le_mono_r  : Nfacts.

Hint Rewrite
     N.sub_0_r N.sub_diag N.mod_0_l N.mod_mod
     N.div2_succ_double N.div2_double
     N.add_1_r N.add_1_l
     N.add_0_r N.add_0_l
     N.pow_add_r
     N.pow_succ_r : Nrewrites.



Ltac crush :=
  repeat (
      try intros;
      eauto with Nfacts;
      autorewrite with Nrewrites;
      try (simpl; f_equal);
      match goal with
      | [ _ : ?P |- ?P ] => assumption
      | [ |- (?n + ?p < ?m + ?q)%N ] => apply (N.add_lt_mono n m p q)
      | [ |- (?n * ?p < ?m * ?q)%N ] => apply (N.mul_lt_mono n m p q)
      | [ |- positive -> _ ] => let p := fresh "p" in intro p
      | [ |- N -> _ ] => let n := fresh "n" in intro n
      | [ p : positive |- _ ] => induction p
      | _ => idtac
      end; eauto with Nfacts).

Lemma of_nat_le_mono: forall a b, a <= b -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intros a b aleb.
  Hint Rewrite Nat2N.inj_succ : Nrewrites.
  induction aleb; crush.
Qed.

Hint Resolve of_nat_le_mono : Nfacts.

Lemma inj_size : forall x, N.of_nat (N.size_nat x) = N.size x.
Proof.
  intro x; induction x;
    assert (forall p, Pos.of_succ_nat (Pos.size_nat p) = Pos.succ (Pos.size p));
  crush.
Qed.

Lemma N_2_neq_0 : (2 <> 0)%N.
Proof.
  intro Hyp; inversion Hyp.
Qed.

Hint Resolve N_2_neq_0 : Nfacts.

Lemma N_pow_2_neq_0 : forall n, (2^n <> 0)%N.
Proof.
  crush.
Qed.

Lemma Npow_2_le_mono : forall a b, (a <= b -> 2^a <= 2^b)%N.
Proof.
  crush.
Qed.

Lemma Npow_2_le_mono_nat : forall a b, a <= b -> (2^(N.of_nat a) <= 2^(N.of_nat b))%N.
Proof.
  crush.
Qed.

Hint Resolve Npow_2_le_mono : Nfacts.

Lemma Nsize_pow_2 n x : (N.size x <= n -> x < 2^n)%N.
Proof.
  intros; assert (2^N.size x <= 2^n)%N;assert (x < 2^ N.size x)%N; crush.
Qed.

Hint Resolve Nsize_pow_2 : Nfacts.

Lemma Nsize_nat_pow_2  n x : N.size_nat x <= n -> (x < 2^(N.of_nat n))%N.
Proof.
  intros; assert (N.size x <= N.of_nat n)%N;
  try (rewrite <- inj_size);
  crush.
Qed.

Hint Resolve Nsize_nat_pow_2 : Nfacts.

Lemma Ndouble_twice : forall (x : N),  (x + x = 2 *x)%N.
  intro;
    apply N2Nat.inj.
  autorewrite with Nnat.
  crush.
Qed.


Lemma Nadd_bound n a b :  (N.size a <= n -> N.size b <= n
                           -> (a + b) < 2^(1+n))%N.
Proof.
  intros.
  Hint Resolve N.add_le_mono : Nfacts.
  autorewrite with Nrewrites.
  rewrite <- Ndouble_twice.
  crush.
Qed.

Lemma Nadd_bound_gen n m a b :  (n < m -> N.size a <= n -> N.size b <= n
                            -> (a + b) < 2^m)%N.
Proof.
  intros.
  Hint Resolve Npow_2_le_mono : Nfacts.
  Hint Resolve N.le_succ_l : Nfacts.
  Hint Resolve Nadd_bound : Nfacts.
  assert (a + b  < 2^(1+n))%N by eauto with Nfacts.
  assert (1+n <= m)%N by (crush; now apply N.le_succ_l).
  assert (2^(1+n) <= 2^m)%N by now apply (Npow_2_le_mono (1+n) m)%N.
  crush.
Qed.

Lemma Nadd_bound_nat n a b : N.size_nat a <= n -> N.size_nat b <= n
                               -> ((a + b) < 2^(N.of_nat (S n)))%N.
Proof.
  autorewrite with Nrewrites;
  try (rewrite <- Ndouble_twice);
  crush.
Qed.


Lemma Nadd_bound_nat_gen n m a b : n < m -> N.size_nat a <= n -> N.size_nat b <= n
                               -> ((a + b) < 2^(N.of_nat m))%N.
Proof.
  intros.
  Hint Resolve Npow_2_le_mono_nat : Nfacts.
  Hint Resolve Nadd_bound_nat : Nfacts.
  assert(a+b < 2^N.of_nat (S n))%N; crush.
Qed.

Lemma Nmul_bound n0 n1 a b :  (N.size a <= n0 -> N.size b <= n1
                               -> (a * b) < 2^(n0 + n1))%N.
Proof.
  crush.
Qed.

Lemma Nmul_bound_nat n0 n1 a b :  N.size_nat a <= n0 -> N.size_nat b <= n1
                               -> ((a * b) < 2^(N.of_nat (n0 + n1)))%N.
Proof.
  Hint Rewrite Nat2N.inj_add : Nrewrites.
  crush.
Qed.
