(* begin hide *)
Require Import PeanoNat.
Import EqNotations.

(* end hide *)

(** * Abstract state machines.

One way to give semantics to verse is through an abstract state
transformation machine, a machine with infinitely many registers, one
for each natural number. Each of these registers have an associated
type and only hold values of that type. What we really have therefore
is a *family* of abstract machines parameterised on the types that we
assign to these registers. The type given below is the type of the
abstract machine.

 *)

Definition type := nat -> Type.

(** ** The state of the machine.

Given an abstract machine belonging to the family [fam], the state of
the machine is an assignment of values to the registers consistent with [fam].

*)

Definition state (typ : type) := forall reg, typ reg.

(** An abstract instruction for the machine is just a state
transformation. Being a monoid, a program is composed of instructions
and hence is also a state transformation.

*)

Definition instruction (typ : type) := state typ -> state typ.
Definition program (typ : type)     := instruction typ.


(**  One such instruction is the update of a register with an appropriate value

*)

Definition modify {typ : type} reg (v : typ reg) : instruction typ
    := fun st regp => match Nat.eq_dec reg regp with
                   | left pf => rew pf in v
                   | _       => st regp
                   end.

(** * Semantics.

We build the monoidal semantics of this abstract state machine
machines. We start with the type system.

*)
Require Import Verse.TypeSystem.
Require Import Verse.Monoid.Semantics.

Definition abstract_type_system : typeSystem
  := {| typeOf    := fun k => Type;
        arrayType := fun n _ ty =>  Vector.t  ty n;
        constOf   := fun ty => ty;
        operator  := fun ty n => Vector.t ty n -> ty
     |}.


(** The variables the register set captured by the following inductive type.
 *)
Inductive register (typ : type) : Variables.U abstract_type_system :=
| R : forall k idx, register typ k (typ idx).

Arguments R [typ k].

Require Verse.Ast.

Require Vector.
Import Vector.VectorNotations.
Module Internals.

  Section MachineType.
    Variable typ : type.

    Definition expr  T := Ast.expr  (register typ) T.
    Definition lexpr T := Ast.lexpr (register typ) T.

    Definition lookup {k} {T : typeOf abstract_type_system k}
               (st : state typ)(reg : register typ k T) : T
      := match reg with
         | R idx => st idx
         end.

    Definition updateReg {k} {T : typeOf abstract_type_system k}
               (reg : register typ k T) (v : T) (st : state typ)
      : state typ
      := match reg in (register _ k0 t) return (t -> state typ) with
         | R idx => fun v0 : typ idx => modify idx v0 st
         end v.

    Definition leval {T} (l : lexpr T) (st : state typ) : T
      := match l with
         | Ast.var reg => lookup st reg
         | Ast.deref v idx  => Vector.nth_order (lookup st v) (proj2_sig idx)
         end.

    Fixpoint eval {T} (st : state typ) (e : expr T) :  T
      := match e with
         | Ast.cval c => c
         | Ast.valueOf lv => leval lv st
         | Ast.app o args => o (Vector.map (eval st) args)
         end.

    Definition assign {T} (l : lexpr T) (e : expr T)(st : state typ) : state typ
      := match l in Ast.lexpr _ T0 return  T0 -> state typ with
         | Ast.var reg  => fun v => updateReg reg v st
         | Ast.deref a idx => fun v => let arr := lookup st a in
                                   let arrp := Vector.replace_order arr (proj2_sig idx) v in
                                   updateReg a (arrp) st
         end (eval st e).

    Definition update {T} (l : lexpr T){arity}
               (o : operator abstract_type_system T (S arity))
               (args : Vector.t (expr T) arity)(st : state typ) : state typ
      := let rhs := Ast.app o (Ast.valueOf l :: args) in
         assign l rhs st.

  End MachineType.
End Internals.
