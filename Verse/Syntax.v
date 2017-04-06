Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Cat.
Require Import FunctionalExtensionality.
Require Import Basics.
Require Import List.
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


(**

We can give a categorical structure on variables with substitutions
being the morphisms. We give this below.

 *)

Module VarT <: Cat.

  Definition o := varT.


  Definition mr (u v : o) := subT u v.

  Definition idM {u : o} : mr u u := fun t x => x.

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



(** *** Abstract syntax trees.

For any language, we can capture the abstract syntax tree using a data
type. A type that captures some abstract syntax has variables embedded
in it. We abstract out this variable type. Thus an abstrct syntax is a
type say [ast] from [varT] to [Type].

Notice that both [varT] and [Type] are (objects) of the associated
categories. If [ast] is an abstract syntax, then a substitution @subT
v w@ for variable types @v@ and @w@, should give us a functorial map
from @ast v@ to @ast w@ which replaces every occurance of the variable
@v@ with @w@. Thus ast's should give us a functor.

*)

Module Type VarTto (C : Cat) := Functor VarT C.
Module Type VarTtoT := VarTto TypeCat.

Definition opSubT (v w : varT) := forall ty, v ty -> option (w ty).

Module Type AST <: VarTtoT.


  Include VarTtoT.

  Parameter vSet : forall {v},  omap v -> Ensemble (sigT v).

  Definition usedIn {v} (o : omap v) (var : sigT v) := In _ (vSet o) var.
  Definition undef {v w} (f : opSubT v w) (var : sigT v) := f _ (projT2 var) = None.

  Arguments vSet / _ _ _ : simpl nomatch.
  Arguments usedIn / _ _ _.
  Arguments undef / _ _ _ _.

  Definition opt {v w : varT} (f : opSubT v w) (o : omap v) :=
    omap w + {exists var : sigT v, usedIn o var /\ undef f var}.

  Parameter opmap : forall {v w} (f : opSubT v w) (o : omap v), opt f o.

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

Module ListF (Syn : VarTtoT) <: VarTtoT.

  Definition omap v := list (Syn.omap v).

  Definition mmap {u v}(f : VarT.mr u v) (lsyn : list (Syn.omap u) ) : list (Syn.omap v)
    := List.map (Syn.mmap f) lsyn.

  Arguments mmap / {u v} _ _.

  Lemma idF {u : VarT.o} : mmap (@VarT.idM u) = TypeCat.idM.
  Proof.
    Hint Rewrite List.map_id.
    Hint Rewrite @Syn.idF.

    crush_ast_obligations.

  Qed.

  Lemma functorial {u v w}{g : subT v w}{f : subT u v}: mmap (g << f) = compose (mmap g) (mmap f).
  Proof.
    Hint Rewrite List.map_map.
    Hint Rewrite @Syn.functorial.

    crush_ast_obligations.
  Qed.

End ListF.

Module ListAST (Syn : AST) <: AST.

  Include ListF (Syn).

  Definition vSet {var} (b : omap var) :=
    fold_right (Union _) (Empty_set _) (map Syn.vSet b).

  Definition usedIn {v} (o : omap v) (var : sigT v) := In _ (vSet o) var.
  Definition undef {v w} (f : opSubT v w) (var : sigT v) := f _ (projT2 var) = None.

  Arguments vSet / _ _ _ : simpl nomatch.
  Arguments usedIn / _ _ _.
  Arguments undef / _ _ _ _.

  Definition opt {v w : varT} (f : opSubT v w) (o : omap v) :=
    omap w + {exists var : sigT v, usedIn o var /\ undef f var}.

  Fixpoint opmap {v w : varT} (f : opSubT v w) (o : list (Syn.omap v)) : opt f o.
    refine
    match o with
    | nil      => {- nil -}
    | oh :: ol => match Syn.opmap f oh, opmap _ _ f ol with
                  | error ev, _ => error _
                  | _, _ => {- nil -}
                  end
    end.
    destruct ev as [ evv evp ].
    destruct evp as [ evi evn ].
    refine (ex_intro _ evv _).
    simpl. eauto.
    Qed.

End ListAST.
(*
Module Opt <: VarTtoT.

  Definition omap := opt.

  Definition mmap {u v}(f : VarT.mr u v) (ou : opt u) : opt v :=
    match ou with
    | {- xU -} => {- f _ xU -}
    | _|_    => _|_
    end.


  Lemma idF {u}: mmap (@VarT.idM u) = id.
  Proof.

    crush_ast_obligations.

  Qed.

 Lemma functorial {u v w}{g : subT v w}{f : subT u v}: mmap (g << f) = compose (mmap g) (mmap f).
  Proof.

    crush_ast_obligations.

  Qed.

End Opt.
*)


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
