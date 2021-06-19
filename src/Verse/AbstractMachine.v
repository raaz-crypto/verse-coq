(* begin hide *)

Require Import Verse.Ast.
Require Import Verse.Language.Pretty.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Monoid.Semantics.
Require Import PeanoNat.

Require Import EqdepFacts.
Import EqNotations.

(* end hide *)

Definition eq_dec T := forall x y : T, x = y \/ ~ x = y.
Section EqDep2.
  (* TODO change names to show the use-case (kind type var *)
  Variable U : Type.
  Variable P : U -> Type.
  Variable Q : forall u, P u -> Type.

  Definition eq_dep2 (p:U) (x:P p) (a:Q _ x)
            (q:U) (y:P q) (b : Q _ y)
    : Prop.
  refine (forall (e:q = p) (f:rew e in y = x),
             a = _).
  subst q.
  simpl in f.
  subst y.
  exact b.
  Defined.
End EqDep2.

Arguments eq_dep2 [U P Q p x] _ [q y].

(** * Semantics.

We build the monoidal semantics of this abstract state machine
machines. We start with the type system.

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

Section Store.

  (** * Abstract state machines.

One way to give semantics to verse is through an abstract state
transformation machine, parametrized on a variable type.

 *)
  Variable ts : typeSystem.
  Variable v : Variables.U ts.
  Variable tyD : typeDenote ts.

  Definition type := typeOf ts.

  Class Store str := { store : str }.

  Definition SPair A : Type := (Store A)*(Store A).
  Class StoreP str := { oldAndNew : SPair str }.

  Coercion Build_StoreP : SPair >-> StoreP.

  Class State :=
    {
      str : Type;
      val  : forall (Str : Store str)
                     {k} {ty : type k} (var : v _ ty),
              typeTrans tyD ty : Type;
      storeUpdate
      : forall {k} {ty : type k} (var : v _ ty)
               (f : typeTrans tyD ty -> typeTrans tyD ty),
          Store str -> Store str;

      evalUpdate
      : forall (s : Store str) k (ty : type k) (var : v _ ty) f,
          forall k' (ty' : type k') (v' : v _ ty'),
            ( ~ eq_dep2 var v'-> val (storeUpdate var f s) v' = val s v')
            /\
            val (storeUpdate var f s) var = f (val s var)

    }.

(** An abstract instruction for the machine is just a state
transformation. Being a monoid, a program is composed of instructions
and hence is also a state transformation.

*)

  Definition instruction `{State} := Store str -> Store str.

  Definition assertion `{State}   := SPair str -> Prop.

End Store.

Arguments State [ts].
Arguments str {ts v tyD State}.
Arguments val [ts v tyD] {State Str} [k ty].
Arguments storeUpdate [ts v tyD] {State} [k ty].
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

    Definition leval {T} (l : lexpr T) (st : Store str) : typeTrans tyD T
      := match l with
         | Ast.var reg      => val reg
         | Ast.deref v idx  => Vector.nth_order
                                 (rew [id] arrayCompatibility tyD _ _ _ in val v)
                                 (proj2_sig idx)
         end.

    Fixpoint evalE {T} (st : Store str) (e : expr T) :  typeTrans tyD T
      := match e with
         | Ast.cval c => constTrans tyD c
         | Ast.valueOf lv => leval lv st
         | Ast.binOp o e0 e1 => (opTrans tyD o) (evalE st e0) (evalE st e1)
         | Ast.uniOp o e0    => (opTrans tyD o) (evalE st e0)
         end.

    Definition assign {T} (l : lexpr T) (e : expr T)(st : Store str)
      : Store str
      := match l in Ast.lexpr _ T0 return  typeTrans tyD T0 -> Store str with
         | Ast.var reg  => fun v => storeUpdate reg (fun _ => v) st
         | Ast.deref a idx => fun v => let arr := val a in
                                       let arrp := Vector.replace_order
                                                     (rew [id] arrayCompatibility tyD _ _ _ in arr)
                                                     (proj2_sig idx) v in
                                       storeUpdate a (fun _ =>
                                                        (rew <- [id] arrayCompatibility tyD _ _ _ in arrp)
                                                     ) st
         end (evalE st e).

    Definition binopUpdate {T}
               (l : lexpr T)
               (o : operator ts T 2)
               (e : expr T)
      : Store str -> Store str
      := let rhs := Ast.binOp o (Ast.valueOf l) e in
         assign l rhs.

    Definition uniopUpdate {T}
               (l : lexpr T)
               (o : operator ts T 1)
      : Store str -> Store str
      := let rhs := Ast.uniOp o (Ast.valueOf l) in
         assign l rhs.

    Definition move {T}(l : lexpr T)(r : v direct T) :=
      assign l (Ast.valueOf (Ast.var r)).

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

  Variable tyD   : typeDenote ts.
  Variable state : State v tyD.

  Definition mline
    := (instruction state * assertion (ts := ts) state)%type.

  Definition justInst
    : instruction state -> mline
    := fun i => (i, fun _ => True).

  Coercion justInst : instruction >-> mline .

  Definition store_machine
    : mSpecs ts ts
    := {|
        mvariables   := v;
        mtypeCompiler := injector ts;
      |}.

  Instance store_interface
    : Interface (ltypes := ts) v store_machine
    := Build_Interface _ _ _ store_machine
                       (@Variables.embed ts v).

  Definition store_semantics
    : Semantics store_machine mline
    := Build_Semantics _ _ store_machine
                       mline _ _
                       ((Internals.denoteStmt ts _ tyD state) >-> justInst)
                       (fun ml => (fst ml, fun stp =>
                                             (snd ml) (snd stp, snd stp)))
  .

End Machine.

Arguments mline {ts v tyD state}.
Arguments store_machine [ts].
Arguments store_interface {ts v}.
Arguments store_semantics {ts v tyD state}.

(* These following definitions are not meant to be exposed
   to the user coding in Verse.
   Thence the prefix 'Int' for 'internal'
*)
Definition IntAnnotation (cv : Variables.U verse_type_system) tyD
  := forall `(State verse_type_system cv tyD),
    line cv mline.

Definition IntAnnotatedCode (cv : Variables.U verse_type_system) tyD
  := forall `(State verse_type_system cv tyD),
    lines cv mline.
(* TODO - Why does this not work without the backtick?
          Does not work with '_ : State ..' but does with 'x : State ...'!
*)

(* Notations for annotations *)

Notation "'OLDVAL' v" := (@val _ _ _ _ (fst oldAndNew) _ _ v) (at level 50).
(* TODO - VAL level has to be changed to be stronger than that of '='
          and of b itvector arithmetic notations *)
Notation "'VAL' v" := (@val _ _ _ _ (snd oldAndNew) _ _ v) (at level 50).

Tactic Notation "annotated_verse" uconstr(B)
  := refine (fun _ => B : lines _ mline); repeat verse_simplify; verse_print_mesg.

Notation "'ASSERT' P" := (inline (id , ((fun (_ : StoreP str) => P) : StoreP str -> Prop) : SPair str -> Prop)) (at level 100).

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

  Definition interpret (prog : Ast.lines v mline)
    := linesDenote (store_machine v) mline store_semantics prog.

End ForAllCxt.

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

(** Tactics for proof goal presentation *)
Require Import Verse.BitVector.
Require Import Verse.BitVector.ArithRing.

(* Destruct the variable store for easier access to valuations *)

Fixpoint prodn T n : Type
  := match n with
     | 0   => Datatypes.unit
     | S n => (T * prodn T n)%type
     end.

Fixpoint lamn T n : (prodn T n -> Type) -> Type
  := match n as n0 return (prodn T n0 -> Type) -> Type with
     | 0   => fun f => forall t, f t
     | S n => fun f => forall t : T, lamn T n (fun x => f (t, x))
     end.

Lemma forallprod T n f
  : lamn T n f
    ->
    forall x : prodn T n, f x.
  induction n.
  easy.
  intros.
  pose (IHn _ (X (fst x)) (snd x)).
  rewrite surjective_pairing.
  exact f0.
Qed.

Ltac prodsize x :=
  match x with
  | (_ * ?t)%type  => let tt := prodsize t in constr:(S tt)
  | Datatypes.unit => constr:(0)
  end.

Ltac breakStore :=
  simpl str;
  let n := fresh "n" in
  match goal with
  | |- forall _ : ?t, _ => let n := prodsize t in pose n
  end; apply (forallprod _ n);
  unfold lamn.

Ltac simplify := repeat match goal with
                        | |- forall _ : str, _ =>
                          breakStore;
                          lazy -[
                            BVplus BVminus BVmul BVquot
                            BVrotR BVrotL BVshiftL BVshiftR BVcomp
                            zero one
                            (*
                            fromNibbles
                              numBinOp numUnaryOp numBigargExop numOverflowBinop
                              Nat.add Nat.sub Nat.mul Nat.div Nat.pow
                              N.add N.sub N.mul N.div N.div_eucl N.modulo

                              Ox nth replace
                             *)
                          ];
                          repeat
                            (match goal with
                             | |- _ /\ _          => constructor
                             | |- _ -> _          => intro
                             | H : _ /\ _ |- _    => destruct H
                             | H : True |- _      => clear H
                             | |- True            => constructor
                             | |- ?x = ?x         => trivial
                             | H : True |- _           => clear H
                             | H : Datatypes.unit |- _ => clear H
                             end)
                        | |- forall _, _ => intro
                        | |- ?I          => unfold I
                        (* The next simply takes care of a functional
                           application. Should only be used once for
                           `tpt`
                        *)
                        | |- context f [ ?F _ ] => unfold F
                        end.
