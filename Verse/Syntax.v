Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Cat.
Require Import FunctionalExtensionality.
Require Import Basics.
Require Import List.
Import  ListNotations.
Require Import Coq.Sets.Ensembles.

(** * Syntactic types.

In this module, we define coq types that captures various syntactic
objects in verse namely variables, languages, substitutions etc.


 *)




(** ** Variable type.

Programs use variables.  The type [varT] captures coq types that can
potentially be variables in programs. It takes as parameter the [type]
of the value that the variable is required to hold.

 *)

Definition varT := type -> Type.



(**

A user first defines an inductive type whose constructors are the
variable she intends to use in the program. For example, suppose she
wishes to write a program which use two variables A and B of types
[Word32] and [Word64] respectively, she would begin with a definition
of the following nature:



<<

Inductive Var : varT :=
| A : Var Word32
| B : Var Word64 .

>>


Defining variables as above helps the user avoid problems like name
clashing (guranteed by each constructor being a name).

*)

(** ** Substitutions

One of the most important operations on variables is
substitution. Variable substitutions are captured by the following
type. The type [subT u v] is the coq type that captures substitutions
from variables of type [u] to variables of type [v]. Subsitutions are
required to preserve the types of the variables.

 *)


Definition subT (u v : varT) := forall t, u t -> v t.

(** The trivial substitution *)

Definition idSubst {v : varT} : subT v v := fun _ vt => vt.

(**

When programs are run on machines, the variables in the program can
either be on stack or in one of the registers of the machine.  The
type [machineVar] is an inductive type parameterised by the underlying
machine registers, that represent program variables.

*)
Inductive machineVar (reg : varT) : varT :=
| onStack    {t : type} : nat   -> machineVar reg t
| inRegister {t : type} : reg t -> machineVar reg t
.

Arguments onStack [reg t] _.

(**

We can give a categorical structure on variables with substitutions
being the morphisms. We give this below.

 *)

Module VarT <: Cat.

  Definition o := varT.


  Definition mr (u v : o) := subT u v.

  Definition idM {u} := @idSubst u .

  Definition composeM {u v w} (g : mr v w)(f : mr u v) : mr u w :=
    fun t ut => g t (f t ut).

  Lemma identityLeft  : forall {a b}{f : mr a b}, composeM idM f =  f.
  Proof. auto. Qed.

  Lemma identityRight : forall {a b}{f : mr a b},  composeM f idM =  f.
  Proof. auto. Qed.

  Lemma associativity : forall {a b c d}{f : mr a b}{g : mr b c}{h : mr c d}, composeM (composeM h g) f  = composeM h (composeM g f).
  Proof. auto. Qed.

End VarT.


Notation "f >> g" := (VarT.composeM g f) (at level 40, left associativity).
Notation "f << g" := (VarT.composeM f g) (at level 40, left associativity).



Module Type VarTto (C : Cat) := Functor VarT C.
Module Type VarTtoT := VarTto TypeCat.

(** *** Abstract syntax trees.

Abstract syntax trees are data types where one of the atomic element
is a variable. Hence, the abstract syntaxes of languages are
essentially types parameterised by [varT].

*)

Definition astT := forall v : varT, Type.

Module Type AST.  (* <: VarTtoT. *)

  (** The syntax tree *)
  Parameter syn       : astT.

  (** Abstract syntaxes allow change of variables. For an [a] is an
      abstract syntax, i.e. [a : astT], it should be possible to lift
      a substitution [s: subT v w] to a map from [a v -> a
      w]. Intuitively, this lift just traverses the syntax tree and
      whenever it hits a leaf corresponding to a variable, it performs
      the substitution.

   *)
  Parameter transform : forall {v w}, subT v w ->  syn v -> syn w.

  (** The syntax type together with the function transoform makes any
      abstract syntax tree a functor from the categroy of varialbes to
      the category of types.  *)

  Include Functor VarT TypeCat
  with Definition omap := syn
  with Definition mmap := fun {v w} => @transform v w.

End AST.

Notation error := inright.
Notation "{- X -}" := (inleft X).

(** * Tactic to crush AST proof obligations

When defining the instance for AST, the identity and composition laws
are often straight forward. This tactic crushes them.

 *)

Ltac crush_ast_obligations :=
  repeat (intros; apply functional_extensionality_dep;
         let x := fresh "X" in intro x; destruct x; simpl;
                               unfold id; unfold compose; autorewrite with core; eauto).
Hint Resolve Union_introl Union_intror In_singleton.

(** * Some examples. *)

Module ListAST (Syn : AST) <: AST.
  Definition syn v := list (Syn.syn v).
  Definition transform {v w}(f : subT v w) := List.map (Syn.transform f).

  Definition omap := syn.
  Definition mmap := fun {v w} => @transform v w.

  (* Arguments mmap / {u v} _ _. *)

  Lemma idF {u : VarT.o} : transform (@VarT.idM u) = TypeCat.idM.
  Proof.
    Hint Rewrite List.map_id.
    Hint Rewrite @Syn.idF.
    unfold transform.
    crush_ast_obligations.
  Qed.

  Lemma functorial {u v w}{g : subT v w}{f : subT u v}: transform (g << f) = compose (transform g) (transform f).
  Proof.
    Hint Rewrite List.map_map.
    Hint Rewrite @Syn.functorial.
    unfold transform.
    crush_ast_obligations.
  Qed.

End ListAST.


Section Scoped.

  (** ** Scopes.

  Code fragments like functions or loops have a set of variables that
  are local to that fragment. The types here allow us to construct a
  HOAS style scoped code fragments. Firstly, fix the variable type for
  the code fragment *)

  Variable v : varT.

  (**

      A scoped code fragment of type [CODE] with [n] variables of
  types [t1,..., tn] is an element of the type [v t1 -> v t2 -> ... ->
  v tn -> T].

   *)

  Fixpoint scoped (l : list type)(CODE : Type) : Type :=
    match l with
    | []       => CODE
    | ty :: lt => v ty -> scoped lt CODE
    end.

  (* Some auxiliaries to work with scopes *)
  
  Fixpoint scopedApp {l : list type} {T T' : Type} : scoped l (T -> T') -> scoped l T -> scoped l T' :=
    match l with
    | nil     => fun scf => scf
    | t :: lt => fun scf sc x => (scopedApp (scf x) (sc x))
    end.

  Fixpoint scopedConst (l : list type) {T : Type} (c : T) : scoped l T :=
    match l return scoped l _ with
    | nil     => c
    | t :: lt => fun x => scopedConst lt c
    end.

  Fixpoint scopedAppConst {l : list type} {T T' : Type} (f : T -> T') : scoped l T -> scoped l T' :=
    scopedApp (scopedConst l f).

  Fixpoint merge_scope {l1 l2 : list type} {T : Type} : scoped l1 (scoped l2 T) -> scoped (l1 ++ l2) T := 
    match l1 with
    | nil      => fun x => x
    | t :: l1t => fun x v => merge_scope (x v)
    end.

  Fixpoint split_scope {l1 l2 : list type} {T : Type} : scoped (l1 ++ l2) T -> scoped l1 (scoped l2 T) :=
    match l1 with
    | nil      => fun x => x
    | t :: l1t => fun x v => split_scope (x v)
    end.


  (** ** Allocation

    When generating code corresponding to the code fragment, we need a
    way to allocate variables to. The following type captures an
    allocation of variables of type [t1,...,tn].

   *)

  Fixpoint allocation (l : list type) : Type :=
    match l with
    | []      => unit
    | t :: lt => v t * allocation lt
    end.

  Fixpoint alloc_split l1 l2 : allocation (l1 ++ l2) -> (allocation l1) * (allocation l2) :=
    match l1 return allocation (l1 ++ l2) -> (allocation l1) * (allocation l2) with
    | []      => fun x => pair tt x
    | t :: lt => fun a : allocation ((t :: lt) ++ l2) =>
                   (fun p : allocation lt * (allocation l2) =>
                     pair (pair (fst a) (fst p)) (snd p))
                   (alloc_split lt l2 (snd a))
    end.

  (* This function fills in the variables from an allocation into a scoped code *)

  Fixpoint fill {CODE} {l : list type} : allocation l -> scoped l CODE -> CODE :=
    match l with
    | []       => fun a x => x
    | ty :: lt => fun a x => fill (snd a) (x (fst a))
    end.

End Scoped.
