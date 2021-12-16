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
        (* The inliner should possibly take the scope of the
           called function as an argument.
           Isn't necessary for semantics, but maybe for inlining
        *)
        inliner      : line -> line
     }.

Arguments inliner [types mtypes] [M line] {_ _}.
Arguments denote  [types mtypes] [M line] {_ _}.

Definition codeDenote {types mtypes}
                      (M : mSpecs types mtypes)
                      line `{Monoid line}
                      (sem : Semantics M line)
  : Ast.code (mvariables M) -> line
  := mapMconcat (denote sem).

Fixpoint lineDenote types mtypes
         (M : mSpecs types mtypes)
         line `{Monoid (line (mvariables M))}
         (sem : Semantics M (line (mvariables M)))
         (c : Ast.line (mvariables M) line)
  : line (mvariables M)
  := match c with
     | inst   i => denote sem i
     | inline i => i
     | call f a => inliner sem
                     (mapMconcat
                                 (lineDenote _ _ M _ sem)
                                 (f (mvariables M) a))
     end.

Definition linesDenote types mtypes
         (M : mSpecs types mtypes)
         line `{Monoid (line (mvariables M))}
         (sem : Semantics M (line (mvariables M)))
         (c : Ast.lines (mvariables M) line)
  : line (mvariables M)
  := mapMconcat (lineDenote _ _ _ _ sem) c.

Arguments linesDenote [types mtypes] _ _ {_ _}.
