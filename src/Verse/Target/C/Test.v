(* Testing of C pretty printing *)
Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Import Verse.Target.C.Pretty.
Require Verse.Language.Ast.
Import Ast.Expr.
Import Nibble.

Open Scope c_scope.
Axiom x : Expr.expr.

Compute (convert_to bigE uint32_t (rotateL uint32_t (x, 2))).
Compute (verse_u8 (Ox1,Ox2)).
