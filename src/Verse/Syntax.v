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

  (** A way to apply functions inside a scope *)
  Fixpoint appScoped n (l : Vector.t (some t) n) T1 T2 (f : T1 -> T2)
    : scoped l T1 -> scoped l T2 :=
    match l with
    | []                  => fun s1 => f s1
    | existT _ _ ty :: lt => fun s1 => fun x : v ty => appScoped lt f (s1 x)
    end.

  (** A dummy VariableT that can help instantiate scoped code *)
  Inductive scopeVar : forall {n} (l : Vector.t (some type) n), VariableT :=
  | headVar m (v : Vector.t (some type) (S m)) : scopeVar v (projT2 (hd v))
  | restVar m (v : Vector.t (some type) (S m)) k (ty : type k) : scopeVar (tl v) ty
                                                                 -> scopeVar v ty.

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

  Fixpoint mergeAllocation n1 n2 (l1 : Vector.t (some t) n1) (l2 : Vector.t (some t) n2)
    : allocation l1 -> allocation l2 -> allocation (append l1 l2) :=
    match l1 with
    | []                  => fun _ a   => a
    | existT _ _ ty :: lt => fun a1 a2 => (fst a1, mergeAllocation _ _ (snd a1) a2)
    end.


  Fixpoint mergeScope T n1 n2 (l1 : Vector.t (some t) n1) (l2 : Vector.t (some t) n2)
             {struct l1} : scoped l1 (scoped l2 T) -> scoped (append l1 l2) T :=
    match l1 as l1' return scoped l1' (scoped l2 T)
                           -> scoped (append l1' l2) T with
    | []        => id
    | existT _ _ ty :: lt  => fun x vt => mergeScope _ _ _ (x vt)
    end.

End Scoped.

Arguments appScoped [t0 v n l T1 T2] _ _.
Arguments mergeAllocation [t0 v n1 n2 l1 l2] _ _.
Arguments mergeScope [t0 v T n1 n2 l1 l2] _.

(* This function fills in the variables from an allocation into a scoped code *)

Fixpoint fill (CODE : VariableT -> Type) v n {l : Vector.t (some type) n}
  : allocation v l -> scoped v l (CODE v) -> (CODE v) :=
  match l with
  | []                 => fun a x => x
  | existT _ _ _ :: lt => fun a x => fill CODE v (snd a) (x (fst a))
  end.

Arguments fill [CODE v n l] _ _.

Fixpoint mapAlloc v1 v2 (f : forall k (ty : type k), v1 _ ty -> v2 _ ty)
         n (l : Vector.t (some type) n) : allocation v1 l -> allocation v2 l :=
  match n return forall l : Vector.t (some type) n, allocation v1 l -> allocation v2 l with
  | S n => fun l a1 => (f _ _ (fst a1), mapAlloc v1 v2 f (tl l) (snd a1))
  | 0   => fun l _  => tt
  end l.

(* The dummy allocation for scoped code *)
Fixpoint dummyAlloc {n} (l : Vector.t (some type) n) : allocation (scopeVar l) l :=
  match n return forall l0 : Vector.t (some type) n, @allocation _ _ n l0 with
   | S m => fun l0 => (headVar l0, mapAlloc _ _ (restVar l0) _ (dummyAlloc (tl l0)))
   | 0   => fun _  => tt
  end l.

(* Generic scoped code filled out with the dummy VariableT *)
Definition fillDummy (CODE : VariableT -> Type) n (l : Vector.t (some type) n)
                     (genC : forall v, scoped v l (CODE v)) :=
  fill (dummyAlloc l) (genC (scopeVar l)).

Arguments fillDummy [CODE n l] _.


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
