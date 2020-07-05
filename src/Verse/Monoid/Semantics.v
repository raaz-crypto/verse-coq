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
Require Import Verse.Language.Types.
Require Import Verse.Error.
Require Verse.Ast.

Record Specs (line : Type) `{Monoid line}
  := {
       types        : typeSystem;
       variables    : Variables.U types
     }.

Arguments variables {_ _ _}.
Arguments types {_ _ _}.

Record Semantics {line : Type} `{Monoid line} (specs : Specs line)
  := {
       denote       : Ast.statement (variables specs)  -> line
     }.

Arguments denote {_ _ _ _}.

Class Interface (v : Variables.U verse_type_system)
                {line : Type} `{Monoid line}
                (specs : Specs line)
  := {
      typeCompiler : TypeSystem.compiler verse_type_system
                                         (types specs);
      Var : forall {k} {ty : type k},
          v _ ty -> Variables.result (variables specs)
                                     (typeTrans typeCompiler ty)
     }.

Arguments typeCompiler _ {_ _ _ _}.
Arguments Var _ {_ _ _ _}.

Definition codeDenote {line} `{Monoid line} {specs : Specs line}
           (sem : Semantics specs)
  : Ast.code (variables specs) -> line
  := mapMconcat (denote sem).
