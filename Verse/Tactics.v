(** * Some useful tactics. *)

(**

The tactic ensures that a given assertion is true at a point
trivially.

 *)

Ltac ensure ass tac :=
  (
    let H := fresh "eHyp" in
    (
      assert (H:ass) by (tac; fail "ensure " ass "failed");
      clear H
    )
  ).

(** Ensure that the given assertion is provable trivially *)
Ltac trivially ass := ensure ass trivial.
