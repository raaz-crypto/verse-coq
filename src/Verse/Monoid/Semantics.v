(* * Monoidal semantics.

Verse being a language of essentially straight line programs, can be
given a semantics in terms of monoids. By changing the underlying
monoid, we can use it to give Hoare style semantics on one hand as
well as code generation into target languages on the other hand.

Given a monoid [S], we fix a type system which specifies which member
of the typeSystem indexed family of verse languages we would like to
interpret in [S]. We also fix the variables for these programs. The
meaning of a program is then completely captured by the meaning of a
statement.

 *)

Require Import Verse.Monoid.
Require Import Verse.TypeSystem.
Require Import Verse.Error.
Require Import Verse.Monoid.Interface.
Require Import Verse.Ast.

(* This single field record should possibly be removed *)
Record Semantics {types mtypes} (M : mSpecs types mtypes) line `{Monoid line}
  := {
        denote       : Ast.statement (mvariables M)  -> line;

        (* The repeater is forced to work with an internal `line`
        instead of a `list Ast.statement` because we need the body
        that is repeated to be denoted as normal code.
        *)
        repeater     : nat -> line -> line
     }.

Arguments denote  [types mtypes] [M line] {_ _ _}.

Definition codeDenote {types mtypes}
                      (M : mSpecs types mtypes)
                      line `{Monoid line}
                      (sem : Semantics M line)
  : Ast.code (mvariables M) -> line
  := mapMconcat (denote sem).
