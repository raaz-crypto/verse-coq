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
         | Ast.var reg      => lookup st reg
         | Ast.deref v idx  => Vector.nth_order (lookup st v) (proj2_sig idx)
         end.

    Fixpoint eval {T} (st : state cxt) (e : expr T) :  T
      := match e with
         | Ast.cval c => c
         | Ast.valueOf lv => leval lv st
         | Ast.binOp o e0 e1 => o (eval st e0) (eval st e1)
         | Ast.uniOp o e0    => o (eval st e0)
         end.

    Definition assign {T} (l : lexpr T) (e : expr T)(st : state cxt) : state cxt
      := match l in Ast.lexpr _ T0 return  T0 -> state cxt with
         | Ast.var reg  => fun v => updateReg reg v st
         | Ast.deref a idx => fun v => let arr := lookup st a in
                                   let arrp := Vector.replace_order arr (proj2_sig idx) v in
                                   updateReg a (arrp) st
         end (eval st e).

    Definition binopUpdate {T}
               (l : lexpr T)
               (o : operator abstract_type_system T 2)
               (e : expr T)
      : state cxt -> state cxt
      := let rhs := Ast.binOp o (Ast.valueOf l) e in
         assign l rhs.

    Definition uniopUpdate {T}
               (l : lexpr T)
               (o : operator abstract_type_system T 1)
      : state cxt -> state cxt
      := let rhs := Ast.uniOp o (Ast.valueOf l) in
         assign l rhs.

    Definition move {T}(l : lexpr T)(r : register cxt direct T) :=
      assign l (Ast.valueOf (Ast.var r)).

    Definition denoteInst {T}(inst : Ast.instruction (register cxt)  T) : instruction cxt
      := match inst with
         | Ast.assign l e => assign l e
         | Ast.moveTo l r => move   l r
         | Ast.binopUpdate l o e => binopUpdate l o e
         | Ast.uniopUpdate l o   => uniopUpdate l o
         | Ast.clobber _     => fun x => x
         end.
    Definition denoteStmt (stmt : Ast.statement (register cxt)) : instruction cxt
      := denoteInst (projT2 stmt).
  End MachineType.


End Internals.

Require Import Verse.Monoid.Semantics.

(* Set Typeclasses Debug. *)

Definition variables cxt : Variables.U abstract_type_system := register cxt.

Definition machine_semantics (cxt : context)
  : Semantics (variables cxt) (instruction cxt)
  := {|
      denote := (Internals.denoteStmt cxt)
     |}.

(* begin hide *)
Require Import Verse.Ast.
(* end hide *)

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



Definition typeDenote ts := TypeSystem.translator ts abstract_type_system.

(**

Much like the case of translating into target language, we can follow
a two stage process for translating programs in the source language to
instructions of the abstract machine. First we type translate to get
the same program but in the type system of the abstract machine. Then
we use the machine semantics to compile the code to instructions in
the abstract machine.

 *)


Section ForAllCxt.

  Variable cxt : context.
  Variable ts  : typeSystem.
  Variable tyD : typeDenote ts.

  Definition var : Variables.U ts
    := Variables.Universe.coTranslate tyD (register cxt).

  Definition interpret (prog : code var) : program cxt
    := codeDenote (variables cxt) (machine_semantics cxt) (Code.translate tyD prog).
  (* The type seems to be necessary for any unification involving
  Setoid because a Setoid instance of any type exists, and thus the
  unification problem for the typeclass can proceed without using
  other information from the context *)

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
