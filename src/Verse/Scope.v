Require Import Verse.Language.Types.
Require Vector.
Import Vector.VectorNotations.

Section Scoped.

  (** * Scopes and allocations.

  In processing verse code, we often have code fragments [C] that use
  variables [x₁,...,xₙ] which needs to be finally allocated into
  registers before code generation. A convenient representation of
  such code fragment is using a function [fun x₁ => ... fun xₙ =>
  C]. Register allocation then becomes application of this function to
  appropriate register variables. We define the type [scoped] that is
  the type of all such PHOAS style code fragments. But first, we
  parameterise over the type system and the variable type.

   *)


  Variable ts : typeSystem.
  Variable v  : VariablesOf ts.
  Arguments v [k].

  (** Since variables themselves have types, a scoped code of [n]
      variables themselves are parameterised by a vector of [n] types.
      We call such vector of types as scopeType.

   *)

  Definition scopeType n :=  Vector.t (some (typeOf ts)) n.

  Fixpoint scoped {n} (st : scopeType n)(CODE : Type) : Type :=
    match st with
    | []                  => CODE
    | existT _ _ ty :: lt => v ty -> scoped lt CODE
    end.

  (** An allocation that can be used to satisfy a scoped object of
      [scopeType], [st].
   *)

  Fixpoint allocation {n} (st : scopeType n) : Type :=
    match n as n0 return scopeType n0 -> Type with
    | 0   => fun _  => unit
    | S m => fun v0 => (v (projT2 (Vector.hd v0)) * allocation (Vector.tl v0))%type
    end st.

  (** And such an allocation can be used to "fill" up the variables *)

  Fixpoint fill {CODE} {n} {st : scopeType n}
  : allocation st -> scoped st CODE -> CODE :=
    match st with
    | []             => fun a x => x
    | existT _ _ _:: lt => fun a x => fill (snd a) (x (fst a))
    end.

  Definition emptyAllocation : allocation [] := tt.

  Definition uncurryScope {CODE} {n} {st : scopeType n}
    : scoped st CODE -> allocation st -> CODE
    := fun sc al =>  fill al sc.

End Scoped.

Arguments scoped [ts] _ [n].
(*

(** A way to apply functions inside a scope *)
Fixpoint appScoped n (l : Vector.t (some t) n) T1 T2 (f : T1 -> T2)
  : scoped l T1 -> scoped l T2 :=
  match l with
  | []                  => fun s1 => f s1
  | existT ty :: lt => fun s1 => fun x : v ty => appScoped lt f (s1 x)
  end.

(** A dummy VariableT that can help instantiate scoped code *)
Inductive scopeVar : forall {n} (l : Vector.t (some type) n), VariableT :=
| headVar m (v : Vector.t (some type) (S m)) : scopeVar v (projT2 (hd v))
| restVar m (v : Vector.t (some type) (S m)) k (ty : type k) : scopeVar (tl v) ty
                                                               -> scopeVar v ty.

Fixpoint mergeAllocation n1 n2 (l1 : Vector.t (some t) n1) (l2 : Vector.t (some t) n2)
  : allocation l1 -> allocation l2 -> allocation (append l1 l2) :=
  match l1 with
  | []                  => fun _ a   => a
  | existT ty :: lt => fun a1 a2 => (fst a1, mergeAllocation _ _ (snd a1) a2)
  end.


Fixpoint mergeScope T n1 n2 (l1 : Vector.t (some t) n1) (l2 : Vector.t (some t) n2)
         {struct l1} : scoped l1 (scoped l2 T) -> scoped (append l1 l2) T :=
  match l1 as l1' return scoped l1' (scoped l2 T)
                         -> scoped (append l1' l2) T with
  | []        => id
  | existT ty :: lt  => fun x vt => mergeScope _ _ _ (x vt)
  end.

End Scoped.

Arguments headVar [m v].
Arguments restVar [m v k ty] _.
Arguments appScoped [t0 v n l T1 T2] _ _.
Arguments mergeAllocation [t0 v n1 n2 l1 l2] _ _.
Arguments mergeScope [t0 v T n1 n2 l1 l2] _.


Fixpoint mapAlloc v1 v2 (f : forall k (ty : type k), v1 _ ty -> v2 _ ty)
         n (l : Vector.t (some type) n) : allocation v1 l -> allocation v2 l :=
  match n return forall l : Vector.t (some type) n, allocation v1 l -> allocation v2 l with
  | S n => fun l a1 => (f _ _ (fst a1), mapAlloc v1 v2 f (tl l) (snd a1))
  | 0   => fun l _  => tt
  end l.

(* The dummy allocation for scoped code *)
Fixpoint dummyAlloc {n} (l : Vector.t (some type) n) : allocation (scopeVar l) l :=
  match n return forall l0 : Vector.t (some type) n, @allocation _ _ n l0 with
   | S m => fun l0 => (@headVar _ l0, mapAlloc _ _ (@restVar _ l0) _ (dummyAlloc (tl l0)))
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

Ltac assignRegisters regs  := exact (fun _ => regs).
Ltac statements       s     := exact s.

*)