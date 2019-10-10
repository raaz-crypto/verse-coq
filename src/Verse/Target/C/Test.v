(* Testing of C pretty printing *)
Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Import Verse.Target.C.Pretty.
Require Verse.Language.Ast.
Import Ast.Expr.
Import Nibble.

Open Scope c_scope.

Axiom x : cvar uint8_t.
Axiom arr : cvar (array 42 uint16_t).
Axiom ptr : cvar (ptrToArray 30 uint64_t).
Compute (declare x).
Compute (declare arr).
Compute (declare ptr).

Compute (convert_to bigE uint32_t (rotateL uint32_t (x, 2))).
Compute (verse_u8 (Ox1,Ox2)).
