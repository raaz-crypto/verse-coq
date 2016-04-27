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

Let T be any type and P Q : T -> Prop such that P -> Q.
In many cases, we want an object of the subclass { t : T | Q t }, but what
we have as assumption is { t : T | P t}. This tactic resolves such cases.

 *)


(**

This tactic makes an assertion and tries to solve it with the tactic tact.
If it succeeds it clears assertion, otherwise leaves the

Ltac ensure p tact

**)

(* generate a proof term from assumptions *)

Ltac useAssumption typ :=
  match goal with
    | [H : typ |- _ ] => exact t
  end.

(* Dispose and run given tactic. *)
Ltac dispose :=
  match goal with
    | [ H : ?G |- ?G      ] => assumption
    | _                     => fail "dispose failed"
  end.
