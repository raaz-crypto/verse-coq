Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Basics.
Require Import List.
Import  ListNotations.
Require Import Coq.Sets.Ensembles.

(** * Syntactic types.

In this module, we define coq types that captures various syntactic
objects in verse namely variables, languages, substitutions etc.


 *)




(** ** Variable type.

Programs use variables.  The type [varT] captures coq types that can
potentially be variables in programs. It takes as parameter the [type]
of the value that the variable is required to hold.

 *)

Definition varT := type -> Type.

(** ** Substitutions

One of the most important operations on variables is
substitution. Variable substitutions are captured by the following
type. The type [subT u v] is the coq type that captures substitutions
from variables of type [u] to variables of type [v]. Subsitutions are
required to preserve the types of the variables.

 *)

Definition subT (u v : varT) := forall t, u t -> v t.

(** *** Abstract syntax trees.

Abstract syntax trees are data types where one of the atomic element
is a variable. Hence, the abstract syntaxes of languages are
essentially types parameterised by [varT].

*)

Definition astT := forall v : varT, Type.

(**

When programs are run on machines, the variables in the program can
either be on stack or in one of the registers of the machine.  The
type [machineVar] is an inductive type parameterised by the underlying
machine registers, that represent program variables.

*)
Inductive machineVar (reg : varT) : varT :=
| onStack    {t : type} : nat   -> machineVar reg t
| inRegister {t : type} : reg t -> machineVar reg t
.

Arguments inRegister [reg t] _.
Arguments onStack [reg t] _.

(* Type definition for a list of types from an ensemble and a projection for the same *)

Definition listIn {T : Type} (e : Ensemble T) := list {t : T | In _ e t}.
Definition proj_l {T : Type} {P : T -> Prop} : list {t : T | P t} -> list T := map (@proj1_sig _ _).


  (** ** Scopes.

  Code fragments like functions or loops have a set of variables that
  are local to that fragment. The types here allow us to construct a
  HOAS style scoped code fragments. Firstly, fix the variable type for
  the code fragment *)

Section Scoped.

  Variable v : varT.

  (**

      A scoped code fragment of type [CODE] with [n] variables of
  types [t1,..., tn] is an element of the type [v t1 -> v t2 -> ... ->
  v tn -> T].

   *)

  Fixpoint scoped (l : list type)(CODE : Type) : Type :=
    match l with
    | []       => CODE
    | ty :: lt => v ty -> scoped lt CODE
    end.

  (* Some auxiliaries to work with scopes *)

  Fixpoint scopedApp {l : list type} {T T' : Type} : scoped l (T -> T') -> scoped l T -> scoped l T' :=
    match l with
    | nil     => fun scf => scf
    | t :: lt => fun scf sc x => (scopedApp (scf x) (sc x))
    end.

  Fixpoint scopedConst (l : list type) {T : Type} (c : T) : scoped l T :=
    match l return scoped l _ with
    | nil     => c
    | t :: lt => fun x => scopedConst lt c
    end.

  Fixpoint scopedAppConst {l : list type} {T T' : Type} (f : T -> T') : scoped l T -> scoped l T' :=
    scopedApp (scopedConst l f).

  Fixpoint merge_scope {l1 l2 : list type} {T : Type} : scoped l1 (scoped l2 T) -> scoped (l1 ++ l2) T :=
    match l1 with
    | nil      => fun x => x
    | t :: l1t => fun x v => merge_scope (x v)
    end.

  Fixpoint split_scope {l1 l2 : list type} {T : Type} : scoped (l1 ++ l2) T -> scoped l1 (scoped l2 T) :=
    match l1 with
    | nil      => fun x => x
    | t :: l1t => fun x v => split_scope (x v)
    end.


  (** ** Allocation

    When generating code corresponding to the code fragment, we need a
    way to allocate variables to. The following type captures an
    allocation of variables of type [t1,...,tn].

   *)

  Fixpoint allocation (l : list type) : Type :=
    match l with
    | []      => unit
    | t :: lt => v t * allocation lt
    end.

  Fixpoint alloc_split l1 l2 : allocation (l1 ++ l2) -> (allocation l1) * (allocation l2) :=
    match l1 return allocation (l1 ++ l2) -> (allocation l1) * (allocation l2) with
    | []      => fun x => pair tt x
    | t :: lt => fun a : allocation ((t :: lt) ++ l2) =>
                   (fun p : allocation lt * (allocation l2) =>
                     pair (pair (fst a) (fst p)) (snd p))
                   (alloc_split lt l2 (snd a))
    end.

  (* This function fills in the variables from an allocation into a scoped code *)

  Fixpoint fill {CODE} {l : list type} : allocation l -> scoped l CODE -> CODE :=
    match l with
    | []       => fun a x => x
    | ty :: lt => fun a x => fill (snd a) (x (fst a))
    end.

End Scoped.
