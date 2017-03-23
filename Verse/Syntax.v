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

Module VarT <: Cat.

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

  Definition o := type -> Type.

  (** ** Substitution type.

The type [subT u v] is the coq type that captures substitutions from
variables of type [u] to variables of type [v]

   *)

  Definition mr (u v : o) := forall t, u t -> v t.

  (** For any variable type [u : varT] there is always a identity substitution *)

  Definition idM {u : o} : mr u u := fun t x => x.

  (** Substitutions can be composed *)

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

Definition varT := VarT.o.
Definition subT := VarT.mr.

(** ** Syntactic types.

The type [synT : Type] captures the coq type of syntax trees. If
[progLang : synT], a syntactic type then [prog : progLang] can be seen
as a particular program parameteried by variables, i.e. if in addition
[u : varT], then [prog u] is a fragment that uses the variable type
[u].

 *)

Definition synT := varT -> Type.

(** *** The class of abstract syntax trees.

Not all elements of [synT] are valid syntax trees. The class [AST]
captures those syntactic objects that are abstract syntax trees. There
are types that allow mapping over its variables using a substitution.

*)

Module Type VarTto (C : Cat) := Functor VarT C.

Module Type VarTtoT := VarTto TypeCat.

(*
Inductive opt (v : VarT.o) :=
| defined (t : type) : v t -> opt v
| undefined          : opt v.

Arguments defined [v t] _ .
Arguments undefined [v].
Notation "{- X -}" := (defined X).
Notation "_|_"   := undefined.
 *)

Definition opSubT (v w : varT) := forall ty, v ty -> option (w ty).

Module Type AST <: VarTtoT.

  Include VarTtoT.

  Parameter vSet : forall {var},  omap var -> Ensemble (sigT var).

  Definition opt {v w : varT} (f : opSubT v w) (o : omap v) :=
    omap w + {exists var : sigT v, and (In _ (vSet o) var) (f _ (projT2 var) = None)}.

  Parameter opmap : forall {v w} (f : opSubT v w) (o : omap v), opt f o.
  
End AST.


(** * Tactic to crush AST proof obligations

When defining the instance for AST, the identity and composition laws
are often straight forward. This tactic crushes them.

 *)

Ltac crush_ast_obligations :=
  repeat (intros; apply functional_extensionality_dep;
         let x := fresh "X" in intro x; destruct x; simpl;
                               unfold id; unfold compose; autorewrite with core; eauto).

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

  Definition vSet {var} (b : omap var) :=
    fold_right (Union _) (Empty_set _) (map Syn.vSet b).

  Definition opt {v w : varT} (f : opSubT v w) (o : omap v) :=
    omap w + {exists var : sigT v, and (In _ (vSet o) var) (f _ (projT2 var) = None)}.


  Fixpoint opmap {v w : varT} (f : opSubT v w) (o : list (Syn.omap v)) : opt f o.
    refine
    match o with
    | nil      => inleft nil
    | oh :: ol => match Syn.opmap f oh, opmap _ _ f ol with
                  | inright ev, _ => inright
                                             match ev with
                                             | ex_intro _ var (conj pin pf) => ex_intro _ var (conj _ pf)
                                             end
                  | _, _ => inleft nil
                  end
    end.
    unfold vSet. simpl. 
    unfold In. apply Union_introl. trivial.
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
                                                                