Require Export String.
Require Export Verse.Nibble.
Require Export Verse.Language.
Require Export Verse.TypeSystem.
Require        Verse.Scope.
Export Vector.VectorNotations.
Delimit Scope vector_scope with vector.
Require Export List.
Coercion Vector.to_list : Vector.t >-> list.

(** Some definitions that are need for code generation *)

Definition VariableT := Variables.U verse_type_system.
Definition constant ty := const ty.
Definition Declaration n := Verse.Scope.type verse_type_system n.
Definition Var (v : VariableT) k ty : v k ty -> some (typeOf verse_type_system)
  := fun _ => existT _ k ty.

Arguments Declaration [n].
Arguments Var [v k ty].

(* Require Export Verse.Types. *)
(* Require Export Verse.Types.Internal. *)
(* Require Export Verse.Word. *)
(* Require Export Verse.Error. *)
(* Require Export Verse.Syntax. *)
(* Require Export Verse.PrettyPrint. *)


(* Require Export Nat. *)
