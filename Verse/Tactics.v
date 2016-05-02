(** * Some useful tactics. *)

(**

* Tactics to prove inequalities of nats.

 *)

Ltac leP orig m n :=
  match m with
    | 0
      => match n with
           | 0      => exact (le_n orig)
           | S ?nP  => apply le_S; leP orig 0 nP
         end
    | S ?mP
      => match n with
           | 0     => fail 1 "bad <= predicate"
           | S ?nP => leP orig mP nP
         end
  end.

Ltac proveLE m n := leP m m n.

Ltac simplify := repeat simpl; trivial.

Ltac crush_inequalities :=
  simplify;
  repeat match goal with
           | [ |- ?M <= ?N ] => unfold M; unfold N; proveLE M N
           | [ |- ?M =  ?N ] => unfold M; unfold N; trivial
         end.

Ltac rewrite_equalities db :=
  simplify;
  repeat match goal with
             | [ H  : _      |-  _ ] => rewrite H
             | _
               => simpl; autorewrite with db; trivial
           end.
