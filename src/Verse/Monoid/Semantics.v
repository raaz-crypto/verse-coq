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
Require Verse.Language.Ast.

Class semantics (Sem : Type) `{Monoid Sem}
  := { types     : typeSystem;
       variables : Variables.U types;
       denote    : Ast.statement variables -> Sem
     }.

Require Verse.Language.Ast.

Definition codeDenote {Sem} `{semantics Sem} : Ast.code variables -> Sem
  := mapMconcat denote.
