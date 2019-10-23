(* Testing of C pretty printing *)
Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Import Verse.Target.C.Pretty.
Require Verse.Language.Ast.
Require List.
Import List.ListNotations.
Import Ast.Expr.
Import Nibble.
Require Vector.
Import Vector.VectorNotations.
Open Scope c_scope.

Axiom x : cvar uint8_t.
Axiom arr : cvar (array 42 uint16_t).
Axiom ptr : cvar (ptrToArray 30 uint64_t).
Compute (declare x).
Compute (declare arr).
Compute (declare ptr).

Definition index_ptr := ptrDeref ptr.
Compute (index (index_ptr) 10).
Compute (convert_to bigE uint32_t (rotateL uint32_t (x, 2))).
Compute (verse_const uint8_t (Ox1,Ox2)).
Axiom myfunc : name.
Axiom a : cvar uint8_t.
Axiom b : cvar uint64_t.
Axiom temp : cvar uint8_t.
Axiom vardec : annotation.
Axiom empty  : annotation.
Notation "'variable' 'declarations'" := vardec (only printing, format " 'variable'  'declarations'  ").

Definition e : Expr.expr := app mul [a ; app plus [a ; b]].
Definition stmts :=
  mkBlock vardec [ declareStmt (declare temp); declareStmt (declare a); update bitXor a [e]].
Definition foo : function :=
  void_function myfunc (declare a, declare b)
                 stmts (Some (while b stmts))  (mkBlock empty []).

Compute foo.