(* Testing of C pretty printing *)
Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Verse.Language.Ast.
Require List.
Import List.ListNotations.
Import Ast.Expr.
Import Nibble.
Require Vector.
Import Vector.VectorNotations.

Axiom x : cvar uint8_t.
Axiom arr : cvar (array 42 uint16_t).
Axiom ptr : cvar (ptrToArray 30 uint64_t).

Definition index_ptr := Expr.ptrDeref ptr.
Axiom myfunc : name.
Axiom a : cvar uint8_t.
Axiom b : cvar uint64_t.
Axiom temp : cvar uint8_t.

Definition e : Expr.expr := Expr.app mul [a ; Expr.app plus [a ; b]].
Definition lDec := [ declare temp; declare a; declare ptr ]%list.

Definition stmts := [ assign (Expr.index (Expr.ptrDeref(ptr)) 2) e;
                      update a bitAnd [e]%vector
                    ]%list.

(*
Compute (declare x).
Compute (declare arr).
Compute (declare ptr).
Compute (index (index_ptr) 10).
Compute (convert_to bigE uint32_t (rotateL uint32_t (x, 2))).
Compute (verse_const uint8_t (Ox1,Ox2)).
 *)

Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.

Goal to_print (function myfunc (params [declare temp; declare temp]) (Braces stmts)).
  print.
Abort.
