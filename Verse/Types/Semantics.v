Require Import Verse.Types.Internal.
Require Import BinNat.
Require Vector.
Require Streams.

Print Vector.t.

(**

We now give a semantics of type. The function typeDenote gives a definition from

 *)

Open Scope N.
Fixpoint modulus (n : nat) : N :=
  match n with
    | O   => 2
    | S m => 2 * modulus m
  end.

Definition NBit n := { m : N | m < modulus n }.


Lemma modulus_n_neq_0 (n : nat) : modulus n <> 0.
Proof.
  induction n. compute. intros. inversion H.
  Search ( _ * _ <> _).
  unfold modulus. fold modulus. apply N.neq_mul_0.
  constructor. compute. intro. inversion H. trivial.
Qed.



Search (_ mod _ < _).
Definition binOp {n : nat}(f : N -> N -> N)(a b : NBit n) : NBit n.
  refine(
      match a , b with
        | exist _ aN _, exist _ bN _ =>  exist _ ((f aN bN) mod (modulus n)) _
      end
    ). apply N.mod_lt. apply modulus_n_neq_0.
Qed.


Definition plus {n : nat}(a b : NBit n) : NBit n := binOp N.add a b.


Fixpoint typeDenote (t : type) : Type :=
  match t with
    | word   n      => NBit n
    | vector n tw   => Vector.t (typeDenote tw) n
    | array  n _ tw => Vector.t (typeDenote tw) n
    | sequence tw   => Streams.Stream (typeDenote tw)
  end.
