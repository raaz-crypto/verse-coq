(* begin hide *)
Require Import Verse.Ast.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Scope.
Require Import Verse.Utils.hlist.
Require Import Verse.Abstract.Machine.
Require Import Verse.Monoid.

Require Import PeanoNat.

Require Import EqdepFacts.
Import EqNotations.

(* end hide *)


(**

Verification of verse code is carried out by annotating code with
verification conditions. To begin the process, we need to interpret
verse types as types in Gallina using a type denotation. Given such a
denotation, the PHOAS style verse code is interpreted as interpreted
as instructions to an abstract machine whose states are captured by
hlists as given by the module [Verse.Abstract.Machine].  The hlist
machine is purely defined by the scope of the code that we are
interpreting.  The memory cells then act as the variables in this
context and unlike the generic variable, they can be checked for
equality (hetrogeneous though) and the associated state transitions
are computable.


The "universal" nature of this machine means that this is a natural
semantics to give to our code and hence verification here is
meaningful.

 *)

Section Hlist.

  Context [ts : typeSystem] (sc : Scope.type ts).
  Variable tyD : typeDenote ts.


  Local Definition tyDenote ty := typeTrans tyD (projT2 ty).

  (** The memory of the hlist machine is the state *)
  Definition state    := Machine.memory tyDenote sc.

  (** The associated variable is just addresses into that memory *)
  Definition variable : Variables.U ts := Machine.address sc.

  (** The function that specialises the generic variable in the scoped
      code with the above variable type *)


  Definition specialise [CODE : Variables.U ts -> Type]
             (genC : forall v, scoped v sc (CODE v)) : CODE variable :=
    uncurry (genC variable) (all_membership sc).

  Local Definition type := typeOf ts.

  (** Compute the value of a variable *)
  Definition val (m : state) ty (x : variable ty)
    := index x m.

  (** Update the value of a variable *)
  Definition update ty (x : variable ty) f (m : state)
    := update x m (f (index x m)).

  (** The state transformation *)
  Definition transformation := state -> state.

  (** An assertion is a predicate on state. Here we have a product of
      state because we would like to assert things based on the
      initial value of the state. The first component of the product
      is therefore the initial state.
   *)
  Definition assertion := state * state -> Prop.

  (** The transformations form a monoid and acts on assertions in a
      natural way by transforming the second component state
      pair. Recall that the first component is the initial state and
      hence transformation acts trivially on it *)

  Global Instance assertion_action_op : LActionOp transformation assertion :=
    fun tr asrt => fun oAn => asrt (fst oAn, tr (snd oAn)).

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


(** * Meanings of program statements as machine transformations *)
Module Internals.

  Section MachineType.
    Variable ts : typeSystem.
    Variable sc : Scope.type ts.
    Variable tyD : typeDenote ts.

    Definition expr  T := Ast.expr  (variable sc) T.
    Definition lexpr T := Ast.lexpr (variable sc) T.

    Definition evalE {T} (st : state sc tyD) (e : expr T) :  tyD _ (projT2 T)
      := Ast.Expr.eval (Expr.rename (val st) e).

    Definition assign {T} (l : lexpr T) (e : expr T)(st : state sc tyD)
      : state sc tyD :=
      match l in Ast.lexpr _ T0 return  tyD _ (projT2 T0) -> state _ _ with
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
      : state sc tyD -> state sc tyD
      := let rhs := Ast.binOp o (Ast.valueOf l) e in
         assign l rhs.

    Definition uniopUpdate {T}
               (l : lexpr (existT _ _ T))
               (o : operator ts T 1)
      : state sc tyD -> state sc tyD
      := let rhs := Ast.uniOp o (Ast.valueOf l) in
         assign l rhs.

    Program Definition move {T}(l : lexpr T)(r : variable sc T) :=
      match l in Ast.lexpr _ T0 return variable sc T0 -> _ with
      | var _ as l1     => fun r0 => assign l1 (Ast.valueOf (Ast.var r0))
      | deref _ _ as l1 => fun r0 => assign l1 (Ast.valueOf (Ast.var r0))
      end r.

    Definition denoteInst {T}(inst : Ast.instruction (variable sc) T) : transformation sc tyD
      := match inst with
         | Ast.assign l e => assign l e
         | Ast.moveTo l r => move   l r
         | Ast.binopUpdate l o e => binopUpdate l o e
         | Ast.uniopUpdate l o   => uniopUpdate l o
         | Ast.clobber _     => fun x => x
         end.

    Definition denoteStmt (stmt : Ast.statement (variable sc) ) : transformation sc tyD
      := denoteInst (projT2 stmt).

  End MachineType.

End Internals.

(** ** The verification monoid.

Verification of annotated code involves working with both
transformations as well as assertions. Transformations form a monoid
under composition and assertions form a monoid under the /\ operation.
It turns out that the verification process can also be seen as working
with a monoid namely the semi direct product got by the action of the
transformation on the assertions.




*)
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
