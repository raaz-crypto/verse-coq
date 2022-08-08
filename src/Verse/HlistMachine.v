(* begin hide *)
Require Import Verse.Ast.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Scope.
Require Import Verse.Utils.hlist.
Require Import Verse.Abstract.Machine.
Require Import Verse.Monoid.
Require Import Verse.Monoid.Semantics.

Require Import PeanoNat.

Require Import EqdepFacts.
Import EqNotations.

(* end hide *)


(** Verse code is written universally quantified over the variable
universe. For the purpose of verification, we instantiate the generic
Verse code with a "universal" variable dictated by its scope. We can
also give a computable State for such variables.  *)

Section Hlist.

  Context [ts : typeSystem] (sc : Scope.type ts).

  Variable tyD : typeDenote ts.

  Local Definition tyd ty := typeTrans tyD (projT2 ty).

  Definition memV : Variables.U ts := member sc.

  (* Generic scoped code instantiated with `memV` *)
  Definition fillMemV [CODE : Variables.U ts -> Type]
             (genC : forall v, scoped v sc (CODE v)) :=
    uncurry (genC memV) (all_membership sc).

  Local Definition type := typeOf ts.
  Let tyd ty := typeTrans tyD (projT2 ty).

  Definition str := Machine.memory tyd sc.

  Definition val (m : str) ty (x : memV ty)
    := index x m.

  Definition update ty (x : memV ty) f (m : str)
    := update x m (f (index x m)).

  Definition transformation := str -> str.

  Definition assertion := str*str -> Prop.

  Global Instance assertion_action_op : LActionOp transformation assertion :=
    fun inst ap => fun oAn => ap (fst oAn, inst (snd oAn)).

  Add Parametric Morphism : lact with signature
      SetoidClass.equiv (A:=transformation) ==> SetoidClass.equiv (A:=assertion) ==> SetoidClass.equiv (A:=assertion) as lact_morp.
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

  Global Program Instance assertion_action : LAction transformation assertion :=
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

End Hlist.

Arguments val [ts sc tyD] _ [ty].
Arguments update [ts sc tyD ty].

Require Import Verse.TypeSystem.

Section Evaluation.
  Context {ts : typeSystem}
          (tyD : typeDenote ts).

  Definition evalLexp {T} (l : lexpr (Variables.sigParam tyD) T)
    : tyD _ (projT2 T)
    := match l in (lexpr _ s) return (tyD (projT1 s) (projT2 s)) with
       | var x => x
       | @deref _ _ ty b e v idx =>
           Vector.nth_order
             (rew [fun T0 : Type@{abstract_type_system.u0} => T0]
                  arrayCompatibility tyD b e ty
               in v)
             (proj2_sig idx)
       end.

  Fixpoint eval {T} (e : expr (Variables.sigParam tyD) T)
    :  tyD _ (projT2 T)
    := match e with
       | Ast.cval c => constTrans tyD c
       | Ast.valueOf lv => evalLexp lv
       | Ast.binOp o e0 e1 => (opTrans tyD o) (eval e0) (eval e1)
       | Ast.uniOp o e0    => (opTrans tyD o) (eval e0)
       end.
End Evaluation.

Module Internals.

  Section MachineType.
    Variable ts : typeSystem.
    Variable sc : Scope.type ts.
    Variable tyD : typeDenote ts.

    Let v := memV sc.

    Definition expr  T := Ast.expr  v T.
    Definition lexpr T := Ast.lexpr v T.

    Definition evalE {T} (st : str sc tyD) (e : expr T) :  tyD _ (projT2 T)
      := eval tyD (Expr.rename (val st) e).

    Definition assign {T} (l : lexpr T) (e : expr T)(st : str sc tyD)
      : str sc tyD :=
      match l in Ast.lexpr _ T0 return  tyD _ (projT2 T0) -> str _ _ with
      | Ast.var reg  => fun v => update reg (fun _ => v) st
      | Ast.deref a idx => fun v => let arr := val st a in
                                let arrp := Vector.replace_order
                                              (rew [fun T0 : Type@{abstract_type_system.u0} => T0]
                                                   arrayCompatibility tyD _ _ _
                                                in arr)
                                              (proj2_sig idx) v
                                in
                                update a (fun _ =>
                                            (rew <- [id] arrayCompatibility tyD _ _ _ in arrp)
                                         ) st
      end (evalE st e).

    Definition binopUpdate {T}
               (l : lexpr (existT _ _ T))
               (o : operator ts T 2)
               (e : expr (existT _ _ T))
      : str sc tyD -> str sc tyD
      := let rhs := Ast.binOp o (Ast.valueOf l) e in
         assign l rhs.

    Definition uniopUpdate {T}
               (l : lexpr (existT _ _ T))
               (o : operator ts T 1)
      : str sc tyD -> str sc tyD
      := let rhs := Ast.uniOp o (Ast.valueOf l) in
         assign l rhs.

    Program Definition move {T}(l : lexpr T)(r : v T) :=
      match l in Ast.lexpr _ T0 return v T0 -> _ with
      | var _ as l1     => fun r0 => assign l1 (Ast.valueOf (Ast.var r0))
      | deref _ _ as l1 => fun r0 => assign l1 (Ast.valueOf (Ast.var r0))
      end r.

    Definition denoteInst {T}(inst : Ast.instruction v  T) : transformation sc tyD
      := match inst with
         | Ast.assign l e => assign l e
         | Ast.moveTo l r => move   l r
         | Ast.binopUpdate l o e => binopUpdate l o e
         | Ast.uniopUpdate l o   => uniopUpdate l o
         | Ast.clobber _     => fun x => x
         end.

    Definition denoteStmt (stmt : Ast.statement v) : transformation sc tyD
      := denoteInst (projT2 stmt).

  End MachineType.

End Internals.

Section Machine.

  Variable ts : typeSystem.
  Variable sc : Scope.type ts.

  Variable tyD   : typeDenote ts.

  Definition mline := transformation sc tyD ⋉ assertion sc tyD.

  Definition justInst
    : transformation sc tyD -> mline
    := fun i => semiR i (fun _ => True).

  Definition justAssert
    : assertion sc tyD -> mline
    := fun a => semiR id a.

End Machine.

Arguments mline [ts].
Arguments justInst [ts sc tyD] .
Arguments justAssert [ts sc tyD].
