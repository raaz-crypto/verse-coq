Require Import Verse.Types.Internal.
Require Import BinNat.
Require Vector.
Require Streams.

(**

We now give a semantics of type. The function typeDenote gives a definition from

 *)



Ltac crush_binnat_ineqs := repeat match goal with
                                  | [ H : ?T |- ?T               ] => exact H
                                  | [ |- N.mul _ _ <> 0%N        ] => apply N.neq_mul_0
                                  | [ |- N.lt (N.modulo _ ?A) ?A ] => apply N.mod_lt
                                  | [ |- _ /\ _                  ] => constructor
                                  | [ |- 2%N <> 0%N              ] => compute; let A := fresh "A" in (intro A; inversion A)
                                  | _                              => eauto; idtac
                                  end.


Open Scope N.
Fixpoint modulus (n : nat) : N :=
  match n with
    | O   => 2
    | S m => 2 * modulus m
  end.

Definition NBit n := { m : N | m < modulus n }.




Lemma modulus_n_neq_0 (n : nat) : modulus n <> 0.
Proof.
  induction n; unfold modulus; fold modulus;crush_binnat_ineqs.
Qed.

Hint Resolve modulus_n_neq_0.
Definition binOp {n : nat}(f : N -> N -> N)(a b : NBit n) : NBit n.
  refine(
      match a , b with
        | exist _ aN _, exist _ bN _ =>  exist _ ((f aN bN) mod (modulus n)) _
      end
    ); crush_binnat_ineqs.
Defined.

Definition unaryOp {n : nat}(f : N -> N)(a: NBit n) : NBit n.
  refine(
      match a with
        | exist _ aN _ =>  exist _ ((f aN) mod (modulus n)) _
      end
    ); crush_binnat_ineqs.
Defined.


Fixpoint typeDenote (t : type) : Type :=
  match t with
    | word   n      => NBit n
    | vector n tw   => Vector.t (typeDenote tw) n
    | array  n _ tw => Vector.t (typeDenote tw) n
    | sequence tw   => Streams.Stream (typeDenote tw)
  end.

(** Meaning of the binary operator at at the given type_ *)

Fixpoint binaryDenote (f : N -> N -> N)(t : type) : typeDenote t -> typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 -> typeDenote t0 with
  | word n        => binOp f
  | vector n tw   => Vector.map2 (binaryDenote f tw)
  | array  n _ tw => Vector.map2 (binaryDenote f tw)
  | sequence tw   => Streams.zipWith (binaryDenote f tw)
  end.

Fixpoint unaryDenote (f : N -> N)(t : type) : typeDenote t -> typeDenote t :=
  match t as t0 return typeDenote t0 -> typeDenote t0 with
  | word n        => unaryOp f
  | vector n tw   => Vector.map (unaryDenote f tw)
  | array  n _ tw => Vector.map (unaryDenote f tw)
  | sequence tw   => Streams.map (unaryDenote f tw)
  end.

Definition plus  := binaryDenote N.add.
Definition minus := binaryDenote N.sub.
