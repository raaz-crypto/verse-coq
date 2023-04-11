Require Import Verse.Monoid.
Require Import Verse.TypeSystem.

Record mSpecs ltypes
  := {
      mtypes       : typeSystem;
      mvariables   : Variables.U mtypes;
      mtypeCompiler : TypeSystem.compiler ltypes mtypes;
     }.
Arguments mtypes [ltypes].
Arguments mvariables [ltypes].
Arguments mtypeCompiler [ltypes].
