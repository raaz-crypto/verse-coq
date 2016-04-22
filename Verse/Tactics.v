(** * Some useful tactics. *)

(**

 Use this tactic for goals of the form A \/ B \/ C.

*)

Ltac ors t :=
  match goal with
    | [ |- ?A \/ ?B ]
      => first [ apply or_introl; ors t | apply or_intror; ors t ]
    | _               => t
  end.

(**

This tactic makes an assertion and tries to solve it with the tactic tact.
If it succeeds it clears assertion, otherwise leaves the

Ltac ensure p tact

**)

(* Dispose and run given tactic. *)
Ltac dispose :=
  match goal with
    | [ H : ?G |- ?G      ] => assumption
    | _                     => fail "dispose failed"
  end.
