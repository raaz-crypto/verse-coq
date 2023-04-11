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
