(* begin hide *)
Require Import PeanoNat.
Import EqNotations.

(* end hide *)

(** * Abstract state machines.

One way to give semantics to verse is through an abstract state
transformation machine, a machine with infinitely many registers, one
for each natural number. Each of these registers have an associated
type and only hold values of that type. This determines the typing
context in which we need to interpret the execution of the
machine. We define the type of contexts below.

 *)

Definition context := nat -> Type.

(** ** The state of the machine.

Given an abstract machine belonging to the family [fam], the state of
the machine is an assignment of values to the registers consistent with [fam].

*)

Definition state (cxt : context) := forall reg, cxt reg.

(** An abstract instruction for the machine is just a state
transformation. Being a monoid, a program is composed of instructions
and hence is also a state transformation.

*)

Definition instruction (cxt : context) := state cxt -> state cxt.
Definition program     (cxt : context) := instruction cxt.


(**  One such instruction is the update of a register with an appropriate value

*)

Definition modify {cxt : context} reg (v : cxt reg) : instruction cxt
    := fun st regp => match Nat.eq_dec reg regp with
                   | left pf => rew pf in v
                   | _       => st regp
                   end.

(** * Semantics.

We build the monoidal semantics of this abstract state machine
machines. We start with the type system.

*)

Require Import Verse.TypeSystem.

Definition abstract_type_system : typeSystem
  := {| typeOf    := fun k => Type;
        arrayType := fun n _ ty =>  Vector.t  ty n;
        constOf   := fun ty => ty;
        operator  := fun ty n => Vector.t ty n -> ty
     |}.


(** The variables the register set captured by the following inductive type.
 *)
Inductive register (cxt : context) : Variables.U abstract_type_system :=
| R : forall k idx, register cxt k (cxt idx).

Arguments R [cxt k].

Require Verse.Ast.

Require Vector.
Import Vector.VectorNotations.
Module Internals.

  Section MachineType.
    Variable cxt: context.

    Definition expr  T := Ast.expr  (register cxt) T.
    Definition lexpr T := Ast.lexpr (register cxt) T.

    Definition lookup {k} {T : typeOf abstract_type_system k}
               (st : state cxt)(reg : register cxt k T) : T
      := match reg with
         | R idx => st idx
         end.

    Definition updateReg {k} {T : typeOf abstract_type_system k}
               (reg : register cxt k T) (v : T) (st : state cxt)
      : state cxt
      := match reg in (register _ k0 t) return (t -> state cxt) with
         | R idx => fun v0 : cxt idx => modify idx v0 st
         end v.

    Definition leval {T} (l : lexpr T) (st : state cxt) : T
      := match l with
         | Ast.var reg => lookup st reg
         | Ast.deref v idx  => Vector.nth_order (lookup st v) (proj2_sig idx)
         end.

    Fixpoint eval {T} (st : state cxt) (e : expr T) :  T
      := match e with
         | Ast.cval c => c
         | Ast.valueOf lv => leval lv st
         | Ast.app o args => o (Vector.map (eval st) args)
         end.

    Definition assign {T} (l : lexpr T) (e : expr T)(st : state cxt) : state cxt
      := match l in Ast.lexpr _ T0 return  T0 -> state cxt with
         | Ast.var reg  => fun v => updateReg reg v st
         | Ast.deref a idx => fun v => let arr := lookup st a in
                                   let arrp := Vector.replace_order arr (proj2_sig idx) v in
                                   updateReg a (arrp) st
         end (eval st e).

    Definition update {T} (l : lexpr T){arity}
               (o : operator abstract_type_system T (S arity))
               (args : Vector.t (expr T) arity)(st : state cxt) : state cxt
      := let rhs := Ast.app o (Ast.valueOf l :: args) in
         assign l rhs st.

    Definition move {T}(l : lexpr T)(r : register cxt direct T) :=
      assign l (Ast.valueOf (Ast.var r)).

    Definition denoteInst {T}(inst : Ast.instruction (register cxt)  T) : instruction cxt
      := match inst with
         | Ast.assign l e => assign l e
         | Ast.moveTo l r => move   l r
         | Ast.update l o e => update l o e
         | Ast.clobber _     => fun x => x
         end.
    Definition denoteStmt (stmt : Ast.statement (register cxt)) : instruction cxt
      := denoteInst (projT2 stmt).
  End MachineType.


End Internals.

Require Import Verse.Monoid.Semantics.
Instance machine_semantics (cxt : context) : semantics (instruction cxt)
  := {| types     := abstract_type_system;
        variables := register cxt;
        denote    := Internals.denoteStmt cxt
      |}.
