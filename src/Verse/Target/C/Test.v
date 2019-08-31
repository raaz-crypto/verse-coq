(* Testing of C pretty printing *)
Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Import Verse.Target.C.Pretty.
Require Verse.Language.Ast.
Import Ast.Internal.

Open Scope c_scope.
Axiom x : Internal.expr.

Compute (convert_to bigE uint32_t (rotateL uint32_t (x, 2))).
