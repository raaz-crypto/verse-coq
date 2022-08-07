(* begin hide *)

Require Import Verse.Ast.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Monoid.
Require Import Verse.Monoid.Semantics.

Require Import PeanoNat.

Require Import EqdepFacts.
Import EqNotations.

(* end hide *)

Section Evaluation.
  Context {ts : typeSystem}
          (tyD : typeDenote ts).

  Definition evalLexp {T} (l : lexpr (Variables.sigParam tyD) T) : tyD _ (projT2 T)
    := match l in (lexpr _ s) return (tyD (projT1 s) (projT2 s)) with
       | var x => x
       | @deref _ _ ty b e v idx =>
           Vector.nth_order
             (rew [fun T0 : Type@{abstract_type_system.u0} => T0]
                  arrayCompatibility tyD b e ty
               in v)
             (proj2_sig idx)
       end.

  Fixpoint eval {T} (e : expr (Variables.sigParam tyD) T) :  tyD _ (projT2 T)
    := match e with
       | Ast.cval c => constTrans tyD c
       | Ast.valueOf lv => evalLexp lv
       | Ast.binOp o e0 e1 => (opTrans tyD o) (eval e0) (eval e1)
       | Ast.uniOp o e0    => (opTrans tyD o) (eval e0)
       end.
End Evaluation.

Section Store.

  (** * Abstract state machines.

One way to give semantics to verse is through an abstract state
transformation machine, parametrized on a variable type.

 *)
  Variable ts : typeSystem.
  Variable v : Variables.U ts.
  Variable tyD : typeDenote ts.

  Local Definition type := typeOf ts.
  Local Definition tyd ty := typeTrans tyD (projT2 ty).

  Definition Pair A : Type := A * A.
  Class StoreP str := { oldAndNew : Pair str }.

  Coercion Build_StoreP : Pair >-> StoreP.

  Class State :=
    {
      str : Type;
      val  : str -> Variables.renaming v (Variables.sigParam tyD);

      storeUpdate
      : forall {ty : some type} (var : v ty)
               (f : tyd ty -> tyd ty),
          str -> str;

      evalUpdate
      : forall (s : str) (ty : some type) (var : v ty) f,
          forall (ty' : some type) (v' : v ty'),
            ( ~ (existT _ _ v') = existT _ _ var -> val (storeUpdate var f s) _ v' = val s _ v')
            /\
            val (storeUpdate var f s) _ var = f (val s _ var)

    }.

(** An abstract instruction for the machine is just a state
transformation. Being a monoid, a program is composed of instructions
and hence is also a state transformation.

*)

  Definition instruction `{State} := str -> str.

  Definition assertion `{State}   := Pair str -> Prop.

  Global Instance assertion_action_op `{State} : LActionOp instruction assertion :=
    fun inst ap => fun oAn => ap (fst oAn, inst (snd oAn)).

  Add Parametric Morphism `{State} : lact with signature
      SetoidClass.equiv (A:=instruction) ==> SetoidClass.equiv (A:=assertion) ==> SetoidClass.equiv (A:=assertion) as lact_morp.
    unfold lact.
    unfold assertion_action_op; simpl.
    intros P Q.
    intro  PEQ.
    intros tr1 tr2.
    intro trEq.
    intro_destruct.
    rewrite (trEq (s, P s0)).
    now rewrite PEQ.
  Qed.

  Global Program Instance assertion_action `{State} : LAction instruction assertion :=
    {| lact_unit := _  |}.

  Next Obligation.
    intro_destruct; unfold lact. unfold assertion_action_op. intuition.
  Qed.

  Next Obligation.
    intro_destruct. unfold lact. unfold assertion_action_op. intuition.
  Qed.

  Next Obligation.
    intro_destruct; unfold lact; unfold assertion_action_op. intuition.
  Qed.


  Next Obligation.
    intro_destruct; unfold lact; unfold assertion_action_op;
    unfold binop; unfold transition_binop; unfold Basics.compose; simpl. intuition.
  Qed.

End Store.

Arguments State [ts].
Arguments str {ts v tyD State}.
Arguments val [ts v tyD] {State} _ [ty].
Arguments storeUpdate [ts v tyD] {State} [ty].
Arguments instruction {ts v tyD _}.
Arguments assertion {ts v tyD _}.

Require Import Verse.TypeSystem.

Module Internals.

  Section MachineType.
    Variable ts : typeSystem.
    Variable v : Variables.U ts.
    Variable tyD : typeDenote ts.

    Variable state : State v tyD.

    Definition expr  T := Ast.expr  v T.
    Definition lexpr T := Ast.lexpr v T.

    Definition evalE {T} (st : str) (e : expr T) :  tyD _ (projT2 T)
      := eval tyD (Expr.rename (val st) e).

    Definition assign {T} (l : lexpr T) (e : expr T)(st : str)
      : str :=
      match l in Ast.lexpr _ T0 return  tyD _ (projT2 T0) -> str with
      | Ast.var reg  => fun v => storeUpdate reg (fun _ => v) st
      | Ast.deref a idx => fun v => let arr := val st a in
                                let arrp := Vector.replace_order
                                              (rew [fun T0 : Type@{abstract_type_system.u0} => T0]
                                                   arrayCompatibility tyD _ _ _
                                                in arr)
                                              (proj2_sig idx) v
                                in
                                storeUpdate a (fun _ =>
                                                 (rew <- [id] arrayCompatibility tyD _ _ _ in arrp)
                                              ) st
      end (evalE st e).

    Definition binopUpdate {T}
               (l : lexpr (existT _ _ T))
               (o : operator ts T 2)
               (e : expr (existT _ _ T))
      : str -> str
      := let rhs := Ast.binOp o (Ast.valueOf l) e in
         assign l rhs.

    Definition uniopUpdate {T}
               (l : lexpr (existT _ _ T))
               (o : operator ts T 1)
      : str -> str
      := let rhs := Ast.uniOp o (Ast.valueOf l) in
         assign l rhs.

    Program Definition move {T}(l : lexpr T)(r : v T) :=
      match l in Ast.lexpr _ T0 return v T0 -> _ with
      | var _ as l1     => fun r0 => assign l1 (Ast.valueOf (Ast.var r0))
      | deref _ _ as l1 => fun r0 => assign l1 (Ast.valueOf (Ast.var r0))
      end r.

    Definition denoteInst {T}(inst : Ast.instruction v  T) : instruction
      := match inst with
         | Ast.assign l e => assign l e
         | Ast.moveTo l r => move   l r
         | Ast.binopUpdate l o e => binopUpdate l o e
         | Ast.uniopUpdate l o   => uniopUpdate l o
         | Ast.clobber _     => fun x => x
         end.

    Definition denoteStmt (stmt : Ast.statement v) : instruction
      := denoteInst (projT2 stmt).

  End MachineType.

End Internals.

Section Machine.

  Variable ts : typeSystem.
  Variable v  : Variables.U ts.

  Variable tyD   : typeDenote ts.

  Definition mline `{State ts v tyD} := instruction ⋉ assertion.

  Definition justInst `{State ts v tyD}
    : instruction -> mline
    := fun i => semiR i (fun _ => True).

  Definition justAssert `{State ts v tyD}
    : assertion -> mline
    := fun a => semiR id a.

End Machine.

Arguments mline [ts].
Arguments justInst [ts v tyD] {_}.
Arguments justAssert [ts v tyD] {_}.
