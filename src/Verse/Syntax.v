Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Basics.
Require Import List.
Import  ListNotations.
Require Import Coq.Sets.Ensembles.

Set Implicit Arguments.

(** * Syntactic types.

In this module, we define coq types that captures various syntactic
objects in verse namely variables, languages, substitutions etc.


 *)




(** ** Variable type.

Programs use variables.  The type [VariableT] captures coq types that can
potentially be variables in programs. It takes as parameter the [type]
of the value that the variable is required to hold.

 *)

Definition VariableT := forall k, type k -> Type.

(** Helper function that recovers the type of the given variable *)
Definition Var {v : VariableT}{k}{t : type k} : v k t -> some type := fun _ => existT _ _ t.

  (** ** Scopes.

  Code fragments like functions or loops have a set of variables that
  are local to that fragment. The types here allow us to construct a
  HOAS style scoped code fragments. Firstly, fix the variable type for
  the code fragment *)

Section Scoped.


  Variable v : VariableT.

  (**

      A scoped code fragment of type [CODE] with [n] variables of
  types [t1,..., tn] is an element of the type [v t1 -> v t2 -> ... ->
  v tn -> T].

   *)

  Fixpoint scoped (l : list (some type))(CODE : Type) : Type :=
    match l with
    | []       => CODE
    | existT _ _ ty :: lt => v ty -> scoped lt CODE
    end.


  (** ** Allocation

    When generating code corresponding to the code fragment, we need a
    way to allocate variables to. The following type captures an
    allocation of variables of type [t1,...,tn].

   *)

  Fixpoint allocation (l : list (some type)) : Type :=
    match l with
    | []      => unit
    | existT _ _ t :: lt => v t * allocation lt
    end.

  Definition emptyAllocation : allocation [] := tt.

  (* This function fills in the variables from an allocation into a scoped code *)

  Fixpoint fill {CODE} {l : list (some type)} : allocation l -> scoped l CODE -> CODE :=
    match l with
    | []                 => fun a x => x
    | existT _ _ _ :: lt => fun a x => fill (snd a) (x (fst a))
    end.

End Scoped.

Arguments fill [v CODE l] _ _.


(* A variable type that us used as a proxy. This variable is *)

Inductive ProxyVar : VariableT :=
| ProxyV : forall k (ty : type k), ProxyVar ty.

Arguments ProxyV [k] _.

Ltac declare func := apply (func ProxyVar);
                     repeat match goal with
                            | [ |- @ProxyVar ?K ?T] => exact (@ProxyV K T)
                            end.
