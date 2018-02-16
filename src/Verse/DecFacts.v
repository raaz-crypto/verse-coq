Require Import Vector.
Require Import VectorEq.

Section DecFacts.

  Variable T : Type.
  Variable T_dec : forall (a b : T), {a = b} + {a <> b}.
  
  Definition eqdec_eqb := fun a b => if T_dec a b then true else false.
  Definition eqdec_eqbeq : forall a b, eqdec_eqb a b = true <-> a = b.
    unfold eqdec_eqb. intros.
    destruct (T_dec a b);
      unfold iff; split; first [discriminate | contradiction | trivial].
  Defined.

  Definition vec_eq_dec n (v1 v2: t T n) : {v1 = v2} + {v1 <> v2}.
    apply (eq_dec T eqdec_eqb eqdec_eqbeq).
  Defined.

End DecFacts.
