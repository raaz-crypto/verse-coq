Require Import Verse.Monoid.
Require Import Verse.TypeSystem.

(* TODO - mtypes can be taken in again *)
Record mSpecs ltypes mtypes
  := {
      mvariables   : Variables.U mtypes;
      mtypeCompiler : TypeSystem.compiler ltypes mtypes;
    }.

Arguments mvariables [ltypes mtypes].
Arguments mtypeCompiler [ltypes mtypes].

Class Interface {ltypes mtypes}
      (v : Variables.U ltypes)
      (S : mSpecs ltypes mtypes)
  := {
      Var : forall {ty : some (typeOf ltypes)},
        v ty -> Variables.Universe.embed (mvariables S)
                                           (Types.Some.translate (mtypeCompiler S) ty)

      (* This cannot use Universe.inject as if the typeCompiler
         is a true compiler, a Var map would not be possible at
         all!
       *)
  }.
