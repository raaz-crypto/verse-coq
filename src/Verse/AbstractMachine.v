(* begin hide *)

Require Import Verse.Ast.
Require Import Verse.Language.Pretty.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Monoid.
Require Import Verse.Monoid.Semantics.


Require Import PeanoNat.

Require Import EqdepFacts.
Import EqNotations.

(* end hide *)

(** * Semantics.

We build the monoidal semantics of this abstract state machine. The
abstract machine needs to be executed in Coq and hence the machine
types are types in Coq. We therefore have the following type system.

*)

(** The universe of  n-ary operator on a type T *)
Fixpoint nary T (n : nat):=
  match n with
  | 0   => T
  | S m => T -> nary T m
  end.

Definition abstract_type_system : typeSystem
  := {| typeOf    := fun k => Type;
        arrayType := fun n _ ty =>  Vector.t  ty n;
        constOf   := fun ty => ty;
        operator  := nary
     |}.

Definition typeDenote ts := TypeSystem.translator ts abstract_type_system.

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

  Global Instance assertion_action_op `{State} : RActionOp assertion instruction :=
    fun ap inst => fun oAn => ap (fst oAn, inst (snd oAn)).

  Add Parametric Morphism `{State} : ract with signature
      SetoidClass.equiv (A:=assertion)==> SetoidClass.equiv ==> SetoidClass.equiv as ract_morp.
    unfold ract.
    unfold assertion_action_op; simpl.
    intros P Q.
    intro  PEQ.
    intros tr1 tr2.
    intro trEq.
    intro_destruct.
    rewrite trEq.
    apply PEQ.
  Qed.

  Global Program Instance assertion_action `{State} : RAction assertion instruction :=
    {| ract_unit := _  |}.

  Next Obligation.
    intro_destruct; unfold ract. unfold assertion_action_op. intuition.
  Qed.

  Next Obligation.
    intro_destruct. unfold ract. unfold assertion_action_op. intuition.
  Qed.

  Next Obligation.
    intro_destruct; unfold ract; unfold assertion_action_op. intuition.
  Qed.


  Next Obligation.
    intro_destruct; unfold ract; unfold assertion_action_op;
    unfold binop; unfold transition_binop; unfold Basics.compose; simpl. intuition.
  Qed.

End Store.

Arguments State [ts].
Arguments str {ts v tyD State}.
Arguments val [ts v tyD] {State} _ [ty].
Arguments storeUpdate [ts v tyD] {State} [ty].
Arguments instruction [ts v tyD].
Arguments assertion [ts v tyD].

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

    Definition denoteInst {T}(inst : Ast.instruction v  T) : instruction state
      := match inst with
         | Ast.assign l e => assign l e
         | Ast.moveTo l r => move   l r
         | Ast.binopUpdate l o e => binopUpdate l o e
         | Ast.uniopUpdate l o   => uniopUpdate l o
         | Ast.clobber _     => fun x => x
         end.

    Definition denoteStmt (stmt : Ast.statement v) : instruction state
      := denoteInst (projT2 stmt).

  End MachineType.

End Internals.

Require Import Verse.Monoid.
Require Import Verse.Monoid.Semantics.
Require Import Verse.Monoid.Interface.

Section Machine.

  Variable ts : typeSystem.
  Variable v  : Variables.U ts.

  Definition store_machine
    : mSpecs ts ts
    := {| mvariables   := v;
          mtypeCompiler := injector ts;
       |}.

  Variable tyD   : typeDenote ts.

  Definition mline :=
    forall state : State v tyD, instruction state ⋉ assertion state.

  Definition justInst
    : (forall state, instruction state) -> mline
    := fun i => fun st => semiR (i st) (fun _ => True).

  Instance store_interface
    : Interface (ltypes := ts) v store_machine
    := Build_Interface _ _ _ store_machine
                       (@Variables.embed ts v).

  Definition store_semantics
    : Semantics store_machine mline
    := {| denote := ((fun s => fun state =>
                                 Internals.denoteStmt ts
                                                      (mvariables store_machine) tyD state s)
                       >->
                       justInst);

          inliner := fun ml => (fun st => let (mlinst, mlannot) := ml st in semiR  mlinst
                                          (fun stp : _ * _ => let (_, new) := stp in
                                                                      mlannot (new, new)))
       |}.

End Machine.

Arguments mline {ts v tyD}.
Arguments justInst [ts v tyD].
Arguments store_machine [ts].
Arguments store_interface {ts v}.
Arguments store_semantics {ts v tyD}.

(* These following definitions are not meant to be exposed
   to the user coding in Verse.
   Thence the prefix 'Int' for 'internal'
*)
Definition IntAnnotation (cv : Variables.U verse_type_system) tyD
  := (*forall `(State verse_type_system cv tyD),*)
    line cv (fun v => @mline _ v tyD).

Definition IntAnnotatedCode (cv : Variables.U verse_type_system) tyD
  := (*forall `(State verse_type_system cv tyD),*)
    lines cv (fun v => @mline _ v tyD).
(* TODO - Why does this not work without the backtick?
          Does not work with '_ : State ..' but does with 'x : State ...'!
*)

(* Notations for annotations *)

Notation "'OLDVAL' v" := (@val _ _ _ _ (fst oldAndNew) _ v) (at level 50).
(* TODO - VAL level has to be changed to be stronger than that of '='
          and of b itvector arithmetic notations *)
Notation "'VAL' v" := (@val _ _ _ _ (snd oldAndNew) _ v) (at level 50).

Tactic Notation "annotated_verse" uconstr(B)
  := refine ((*fun _ =>*) B : lines _ (fun v => mline (v := v))); repeat verse_simplify; verse_print_mesg.

Notation "'ASSERT' P" := (inline (fun _ => (id , ((fun (_ : StoreP str) => P) : StoreP str -> Prop) : Pair str -> Prop))) (at level 100).

(** * Language Semantics.

Language semantics is now by translating programs to instructions of
the abstract machine. In our case, we have a family of languages that
are parameterised by the underlying type system.  Any member in this
associated with a structure [ts : typeSystem]. To give meanings to
straight line programs in that language, we only need to specify how
the types in that language is mapped into the types of the abstract
machine system. In other words, all we need is a type translator from
the source language to the [abstract_type_system].

 *)



(**

Much like the case of translating into target language, we can follow
a two stage process for translating programs in the source language to
instructions of the abstract machine. First we type translate to get
the same program but in the type system of the abstract machine. Then
we use the machine semantics to compile the code to instructions in
the abstract machine.

 *)


Section ForAllCxt.

  Variable   v : Variables.U verse_type_system.
  Variable tyD : typeDenote verse_type_system.

  Variable state : State v tyD.

  Definition interpret (prog : Ast.lines v (fun v => @mline _ v tyD))
    := linesDenote (store_machine v)
                   (fun v => @mline _ v tyD)
                   store_semantics
                   prog.

End ForAllCxt.

Arguments interpret [v tyD].

Require Import Verse.Language.Types.

(* ** Semantics for the Verse language.

In the case of the verse language (i.e where our type system is the
[verse_type_system]), we need to only specify the translation for the
[word n] type. We use the [fromWordDenote] function to convert it to
an element of [typeDenote verse_type_system] giving semantics for the
verse language. We define this function inside a section to manage the
verbosity of the types.

*)


Section WordTypeDenote.

  (** We need to give three things to get a [typeDenote
     verse_type_system]

     - A function [wordOfSize] which gives the type associated to the
        verse type [word n],

     - A [const] function which for every [n] gives a way to convert
        the verse constant of type [word n] to [wordOfSize n],

     - A [oper] function that interprets verse operators for [wordOfSize n].

  *)

  Variable wordOfSize : nat -> Type.
  Variable const      : forall sz, constOf verse_type_system (word sz) -> wordOfSize sz.
  Variable oper       : forall sz arity, op arity -> nary (wordOfSize sz) arity.

  Fixpoint typeConv k (ty : type k)  : typeOf abstract_type_system k :=
    match ty with
    | word sz => wordOfSize sz
    | multiword m sz => Vector.t (wordOfSize sz) (2^m)
    | array b e ty  => Vector.t (typeConv direct ty) b
    end.

  Definition constConv (ty : type direct)
    :  constOf verse_type_system ty  -> typeConv direct ty
    := match
        ty as ty0 in (type k)
        return
        (match k as x return (type x -> Type) with
         | direct => fun t : type direct => constOf verse_type_system t -> typeConv direct t
         | memory => fun _ : type memory => IDProp
         end ty0)
      with
      | word n => const n
      | multiword m n => Vector.map (const n)
      | array _ _ _ => idProp
      end.

  Definition vectorApp {A B}{n}(fvec : Vector.t (A -> B) n) (vec : Vector.t A n) : Vector.t B n
    := Vector.map2 (fun f x => f x) fvec vec.
  Fixpoint appN {T} {m} arity : Vector.t (nary T arity) m ->  nary (Vector.t T m) arity
    := match arity with
       | 0 => fun x => x
       | S r => fun fvec vec => appN r (vectorApp fvec vec)
       end.

  Fixpoint opConvGen {k} (ty : type k) arity (o : op arity)
    : nary (typeConv k ty) arity
    := match ty as ty0 in type k0
             return  nary (typeConv k0 ty0) arity
       with
       | word sz =>  oper sz arity o
       | multiword m sz  =>
         appN  arity (Vector.const (oper sz arity o) (2^m))
       | array b e ty0 => appN arity (Vector.const (opConvGen ty0 arity o) b)
       end.
  Definition opConv := @opConvGen direct.

  Definition fromWordDenote :  typeDenote verse_type_system :=
    {| typeTrans  := typeConv;
       constTrans := constConv;
       opTrans    := opConv;
       arrayCompatibility := fun _ _ _ => eq_refl
    |}.
End WordTypeDenote.
