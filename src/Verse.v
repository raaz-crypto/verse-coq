Require Export String.
Require Export Verse.Nibble.
Require Export Verse.Language.
Require Export Verse.TypeSystem.
Require        Verse.Scope.
Export Vector.VectorNotations.
Delimit Scope vector_scope with vector.

Module VerseNotations.
  Open Scope verse_scope.
End VerseNotations.

(* This allows us to use the vector notations for lists as well

<<

Definition foo : Vector.t nat _ := 1 :: [2;3].
Definition bar : list nat := 1 :: [2;3].

>>

*)

Coercion Vector.to_list : Vector.t >-> list.

(** Some definitions that are need for code generation *)

Definition VariableT := Variables.U verse_type_system.
Definition constant ty := const ty.
Definition Declaration n := Verse.Scope.type verse_type_system n.
Definition Var (v : VariableT) ty : v ty -> some (typeOf verse_type_system)
  := fun _ => ty.

Arguments Declaration {n}.
Arguments Var [v ty].

Notation "(--)"             := (tt).
Notation "(- x -)"          := (pair x tt).
Notation "(- x , .. , z -)" := (pair x .. (pair z tt) ..).
Notation "'do' B 'end'"     := (Scope.body B).
