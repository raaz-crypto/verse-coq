Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import FunctionalExtensionality.
Require Import Basics.

(** * Syntactic types.

In this module, we define coq types that captures various syntactic
objects in verse namely variables, languages, substitutions etc.


*)

(** ** Variable type.


Programs use variables.  The type [varT : Type] captures coq types
that can potentially be variables in programs.  A user first defines
an inductive type whose constructors are the variable she intends to
use in the program. For example, suppose she wishes to write a program
which use two variables A and B of types [Word32] and [Word64]
respectively, she would begin with a definition of the following
nature:


<<

Inductive Var : varT :=
| A : Var Word32
| B : Var Word64
.

>>


Defining variables as above helps the user avoid problems like name
clashing (guranteed by each constructor being a name).

*)

Definition varT := type -> Type.

(** ** Substitution type.

The type [subT u v] is the coq type that captures substitutions from
variables of type [u] to variables of type [v]

*)

Definition subT (u v : varT) := forall t, u t -> v t.


(** For any variable type [u : varT] there is always a identity substitution *)

Definition idSubst (u : varT) : subT u u := fun _ x => x.

(** Substitutions can be composed *)
Definition composeSubT {u v w} (g : subT v w)(f : subT u v) : subT u w :=
  fun t ut => g t (f t ut).

Notation "f >> g" := (composeSubT g f) (at level 40, left associativity).
Notation "f << g" := (composeSubT f g) (at level 40, left associativity).



(** ** Syntactic types.

The type [synT : Type] captures the coq type of syntax trees. If
[progLang : synT], a syntactic type then [prog : progLang] can be seen
as a particular program parameteried by variables, i.e. if in addition
[u : varT], then [prog u] is a fragment that uses the variable type
[u].

*)

Definition synT := varT -> Type.
Definition morphT (syn : synT) := varT -> varT -> Type.

(** *** The class of abstract syntax trees.

Not all elements of [synT] are valid syntax trees. The class [AST]
captures those syntactic objects that are abstract syntax trees. There
are types that allow mapping over its variables using a substitution.

*)

Module Type AST.

  (* The type of the underlying syntax tree *)
  Parameter T : Type.
  Parameter syn : varT -> T.
  Parameter morph : forall (T1 T2 : T), Type.

  Parameter idM : forall (T1 : T), morph T1 T1.
  Parameter composeM : forall {T1 T2 T3}, morph T2 T3 -> morph T1 T2 -> morph T1 T3.

  Axiom identityM : forall {T1 T2} {f : morph T1 T2}, and (composeM (idM T2) f = f) (composeM f (idM T1) = f).
  Axiom associativeM : forall {T1 T2 T3 T4} {f : morph T1 T2} {g : morph T2 T3} {h : morph T3 T4}, composeM h (composeM g f) = composeM (composeM h g) f.

  (* The function that maps a subsitution over the syntax tree *)
  Parameter map : forall {u v : varT}, subT u v -> morph (syn u) (syn v).

  Axiom identity : forall {u}, map (idSubst u) = idM (syn u).

  Axiom composition : forall {u v w}{g : subT v w}{f : subT u v}, map (g << f) = composeM (map g) (map f).

End AST.

Module Type ASTT:= AST with Definition T := Type.
Module Type ASTU := ASTT
      with Definition morph := fun T1 T2 => T1 -> T2
      with Definition idM := @id
      with Definition composeM := @compose.

(** * Tactic to crush AST proof obligations

When defining the instance for AST, the identity and composition laws
are often straight forward. This tactic crushes them.

 *)

Ltac crush_ast_obligations :=
  repeat apply functional_extensionality;
         let x := fresh "X" in intro x; destruct x;
                               unfold id; unfold compose; autorewrite with core; eauto.

(** * Some examples. *)

Module ListAST (Syn : ASTU) <: ASTU.

  Definition T := Type.
  Definition morph := fun T1 T2 => T1 -> T2.
  
  Definition idM := @id.
  Definition composeM := @compose.

  Arguments idM [A] _.
  Arguments composeM [A B C] _ _ _.
  
  Lemma identityM {T1 T2} : forall {f : morph T1 T2}, and (composeM (@idM T2) f = f) (composeM f (@idM T1) = f).
  Proof.
    eauto.
  Qed.
  
  Lemma associativeM {T1 T2 T3 T4} : forall {f : morph T1 T2} {g : morph T2 T3} {h : morph T3 T4}, composeM h (composeM g f) = composeM (composeM h g) f.
  Proof.
    eauto.
  Qed.

  
  Definition syn (v : varT) := list (Syn.syn v).

  Definition map {u v}(f : subT u v) (lsyn : list (Syn.syn u) ) : list (Syn.syn v)
    := List.map (Syn.map f) lsyn.

  Lemma identity {u}: map (idSubst u) = id.
  Proof.
    Hint Rewrite List.map_id.
    Hint Rewrite @Syn.identity.

    unfold map.
    crush_ast_obligations.

  Qed.


  Lemma composition {u v w}{g : subT v w}{f : subT u v}: map (g << f) = compose (map g) (map f).
  Proof.
    Hint Rewrite List.map_map.
    Hint Rewrite @Syn.composition.

    unfold map.
    crush_ast_obligations.
  Qed.

End ListAST.

Inductive opt (v : varT) :=
| defined (t : type) : v t -> opt v
| undefined          : opt v.

Arguments defined [v t] _ .
Arguments undefined [v].
Notation "{- X -}" := (defined X).
Notation "_|_"   := undefined.


Module OptAST <: AST.

  Definition T := Type.
  Definition syn := opt.

  Definition morph := fun T1 T2 => T1 -> T2.

  Definition idM := @id.
  Arguments idM [A] _.

  Definition composeM := @compose.

  Arguments composeM [A B C] _ _ _.

  Lemma identityM : forall {T1 T2} {f : morph T1 T2}, and (composeM (@idM T2) f = f) (composeM f (@idM T1) = f).
  Proof.
    eauto.
  Qed.
  
  Lemma associativeM : forall {T1 T2 T3 T4} {f : morph T1 T2} {g : morph T2 T3} {h : morph T3 T4}, composeM h (composeM g f) = composeM (composeM h g) f.
  Proof.
    eauto.
  Qed.

  Definition map {u v}(f : subT u v) (ou : opt u) : opt v :=
    match ou with
    | {- xU -} => {- f _ xU -}
    | _|_    => _|_
    end.


  Lemma identity {u}: map (idSubst u) = id.
  Proof.
    
    crush_ast_obligations.
    
  Qed.

  Lemma composition {u v w}{g : subT v w}{f : subT u v}: map (g << f) = compose (map g) (map f).
  Proof.

    crush_ast_obligations.

  Qed.

End OptAST.

(** A small example of maping over Opt.


<<

Inductive U : varT :=
| xU : U Word32
| yU : U Word64
.

Inductive V : varT :=
| xV : V Word32
| yV : V Word64
.

Print xU.

Print U.
Print V.

Definition fUV : subT U V :=
  fun _ x => match x with
             | xU => xV
             | yU => yV
             end.

Import OptAST.
Module OptListAST := ListAST(OptAST).
Import OptListAST.

Print OptAST.map.
Require Import List.
Import ListNotations.
Compute (OptListAST.map fUV [ {- xU -}; {- yU -}; _|_ ]).

>>

*)
