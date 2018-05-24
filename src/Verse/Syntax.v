Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Basics.
Require Import List.
Import  ListNotations.
Require Import Vector.
Import VectorNotations.
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

Definition GenVariableT (t : kind -> Type):= forall {k : kind}, t k -> Type.
Definition VariableT := GenVariableT type.


(** A declaration is just a sequence of types *)
Definition Declaration              := list (some type).
Definition Empty  : Declaration     := []%list.

(** Helper function that recovers the type of the given variable *)
Definition Var {v : VariableT}{k}{t : type k} : v k t -> some type := fun _ => existT _ _ t.

  (** ** Scopes.

  Code fragments like functions or loops have a set of variables that
  are local to that fragment. The types here allow us to construct a
  HOAS style scoped code fragments. Firstly, fix the variable type for
  the code fragment *)


Section Scoped.

  Variable t : kind -> Type.
  Variable v : GenVariableT t.


  (**

      A scoped code fragment of type [CODE] with [n] variables of
  types [t1,..., tn] is an element of the type [v t1 -> v t2 -> ... ->
  v tn -> T].

   *)

  Fixpoint scoped n (l : Vector.t (some t) n)(CODE : Type) : Type :=
    match l with
    | []                  => CODE
    | existT _ _ ty :: lt => v ty -> scoped lt CODE
    end.

  Inductive scopeVar : forall {n} (l : Vector.t (some type) n), VariableT :=
  | headVar m (v : Vector.t (some type) (S m)) : scopeVar v (projT2 (hd v))
  | restVar m (v : Vector.t (some type) (S m)) k (ty : type k) : scopeVar (tl v) ty.

  (** ** Allocation

    When generating code corresponding to the code fragment, we need a
    way to allocate variables to. The following type captures an
    allocation of variables of type [t1,...,tn].

   *)

  Fixpoint allocation n (l : Vector.t (some t) n) : Type :=
    match n return Vector.t (some t) n -> Type with
    | 0   => fun _  => unit
    | S m => fun v0 => (v (projT2 (hd v0)) * allocation (tl v0))%type
    end l.

  Definition emptyAllocation : allocation [] := tt.

  (* This function fills in the variables from an allocation into a scoped code *)

  Fixpoint fill {CODE} n {l : Vector.t (some t) n} : allocation l -> scoped l CODE -> CODE :=
    match l with
    | []                 => fun a x => x
    | existT _ _ _ :: lt => fun a x => fill (snd a) (x (fst a))
    end.

End Scoped.

Arguments fill [t0 v CODE n l] _ _.

(* A variable type that us used as a proxy. This variable is *)

Inductive ProxyVar : VariableT :=
| ProxyV : forall k (ty : type k), ProxyVar ty.

Arguments ProxyV [k] _.

Ltac declare ps  := match (type of ps) with
                    | VariableT -> _ => apply (ps ProxyVar);
                                repeat match goal with
                                       | [ |- @ProxyVar ?K ?T] => exact (@ProxyV K T)
                                       end
                    | _ => exact []
                    end.

Notation "(--)"             := (tt).
Notation "(- x , .. , z -)" := (pair x .. (pair z tt) ..).

Ltac assignRegisters regs  := exact regs.
Ltac statements       s     := exact s.
