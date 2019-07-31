Set Implicit Arguments.
Require Import TypeSystem.

(** ** Expressions.

We begin defining expressions by defining operators for the expression
language.  Most architectures allow various basic arithmetic and
bitwise operations on values stored in the registers. These operations
are captured by the type [op] which is parameterised by the arity of
the operation.

*)


Inductive op : nat -> Type :=
| plus    : op 2
| minus   : op 2
| mul     : op 2
| quot    : op 2
| rem     : op 2
| bitOr   : op 2
| bitAnd  : op 2
| bitXor  : op 2
| bitComp : op 1
| rotL    : nat -> op 1
| rotR    : nat -> op 1
| shiftL  : nat -> op 1
| shiftR  : nat -> op 1
.

Require Vector.

Section Expr.

  (** Expressions that can occur on the left of an assignment. *)
  Inductive lexpr {ts : typeSystem}(v : VariableT ts) : type ts direct ->  Type :=
  | var   :  forall {ty},  v direct ty -> lexpr v ty  (* Location associated with a variable *)
  | deref :  forall {ty : type ts memory}, v memory ty -> index ts ty -> lexpr v (contentType ts ty).

  (** The expression type *)
  Inductive expr {ts : typeSystem}(v : VariableT ts)(ty : type ts direct) : Type :=
  | cval     : const ts ty -> expr v ty
  | valueOf  : lexpr v ty -> expr v ty
  | app      : forall {arity : nat}, op arity -> Vector.t (expr v ty) arity -> expr v ty.



(** * Expressions

We now define expressions over this operators. This is defined with
respect to the type system.

 *)

End Expr.

Arguments lexpr [ts].
Arguments var [ts v ty].
Arguments deref [ts v ty].

Arguments expr [ts].
Arguments cval [ts v ty].
Arguments valueOf [ts v ty].
Arguments app [ts v ty arity].
