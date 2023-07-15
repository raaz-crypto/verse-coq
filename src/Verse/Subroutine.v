(** * Annotated Code This module gives an AST for Verse code with a
`call`. We leverage the annotated code module already provided in
Verse.AnnotatedCode to provide annotations in the code. The `call`
introduced provides a way to further streamline proofs with
modularity.

The module is written in a generality that will allow it to be used
for specified target specific instructions too. Using the `call`
instructions to package target specific instructions with intended
state transformations and guarantees will allow for proofs with such
instructions.  *)

Require Import Verse.Annotated.
Require Import Verse.Ast.
Require Import Verse.HlistMachine.
Require Import Verse.Language.Types.
Require Import Verse.Monoid.
Require Verse.Scope.
Require Import Verse.TypeSystem.
Require Import Verse.Abstract.Machine.
Require Import Verse.Utils.hlist.

Require Import PList.
Import ListNotations.

(* NOTE : Wrapping this section in a module would need many more name
   changes.  For example, `subroutine` might need to become `t`.  It
   would be better to do that to avoid hard-to-debug bugs involving
   innocuous use of wrong `statement` or `code` in other places. *)
Section Subroutine.

  Context [tyD : typeDenote verse_type_system]
          [ v  : VariableT ].

  Record subroutine w := { blck   : Annotated.code tyD w;
                          postC   : ann tyD w    }.

  Arguments blck [w].
  Arguments postC [w].

  Let sub (sc : Scope.type verse_type_system)
      := Machine.subroutine (tyD : Variables.U verse_type_system) sc sc.

  Let vsub (sc : Scope.type verse_type_system)
    := Machine.vsubroutine (tyD : Variables.U verse_type_system) sc sc.

  Definition func sc
    := forall w, Scope.allocation w sc
                 -> subroutine w.

  Definition funSub sc (fc : func sc) : sub sc
    := let (bl, pc)   := fc (HlistMachine.variable sc) (all_membership sc) in
       {| transform   := srFst (Annotated.codeDenote (sc := sc) bl);
          guarantee   := srSnd (Annotated.statementDenote (annot pc))
       |}.


  Inductive equiv : forall [T], T -> forall [sc], vsub sc -> Type :=
  | call : forall [sc] (fc : func sc)
                  (vc : VC (funSub sc fc)), equiv fc (exist _ _ vc).

  Record vsubroutine := { inTy   : Scope.type verse_type_system -> Type;
                          inSc   : Scope.type verse_type_system;
                          inLine : inTy inSc;
                          verSub : vsub inSc;
                          eqprf  : @equiv _ inLine inSc verSub }.

  Inductive statement :=
  | block         : Annotated.code tyD v -> statement
  | inline        : forall vfun, Scope.allocation v (inSc vfun) -> statement.

  Definition code := list statement.

  (* We consider the default interpretation of a `call` to be an
  inlining of the text of the function while stripping it of its
  annotations. We do this to avoid inadvertant errors and confusion
  arising from the intended meaning of `INIT` values in annotations
  inside functions.
   *)

  Definition stripAnn [v] (ls : Annotated.code tyD v)
    := concat (map (fun l => match l with
                     | inst _ as l0 => [ l0 ]
                     | _            => []
                     end)
                   ls).

  Definition inline_call (a : statement) : Annotated.code tyD v
    := match a with
       | block i       => i
       | inline sl all => match eqprf sl with
                          | call fc vc => fun all0 => stripAnn (blck (fc v all0))
                          end all
       end.

  Definition inline_calls := fun x : code => concat (PList.map inline_call x).

  Lemma inline_instructions (ls : Annotated.code tyD v)
    : inline_calls [ block ls ] = ls.
  Proof.
    unfold inline_calls.
    apply app_nil_r.
  Qed.

End Subroutine.

Arguments postC [tyD w].
Arguments subroutine tyD w : clear implicits.
Arguments statement tyD v : clear implicits.
Arguments code tyD v : clear implicits.
Arguments vsubroutine tyD : clear implicits.

Require Import Verse.Language.Pretty.
Require Verse.Ast.

(* Mapping instances for custom syntax notations *)

#[export] Instance statement_modular tyD (v : VariableT)
  : AST_maps (list (Ast.statement v)) (statement tyD v) | 1
  := {| CODE := fun ls => [ block (CODE ls) ] |}.

#[export] Instance annot_modular tyD (v : VariableT) : AST_maps (ann tyD v) (statement tyD v) | 1
  := {| CODE := fun an => [ block [ annot an ] ] |}.

#[export] Instance statement_repModular tyD (v : VariableT)
  : AST_maps (list (Ast.statement v)) (repeated (list (statement tyD v))) | 0
  := {| CODE := fun ls => [ Repeat.repeat 1 [ block (CODE ls) ] ] |}.

#[export] Instance annot_repModular tyD (v : VariableT) : AST_maps (ann tyD v) (repeated (list (statement tyD v))) | 0
  := {| CODE := fun an => [ Repeat.repeat 1 [ block [ annot an ] ] ] |}.

#[export] Instance modular_id tyD (v : VariableT) : AST_maps (list (statement tyD v)) (statement tyD v) | 1 := {| CODE := id |}.

#[export] Instance modular_repModular tyD (v : VariableT) : AST_maps (list (statement tyD v)) (repeated (list (statement tyD v))) | 0
  := {| CODE := fun x => [ Repeat.repeat 1 x ] |}.

Notation "'CALL' f 'WITH' a" := (CODE [ inline f a ]) (at level 60).

Notation "F 'DOES' Post" := ({| blck := F;
                                postC := fun _ : StoreP (Str _ _) => Post |})
                              (at level 60).

Ltac Pack f := let cv := constr:(fun v => Scope.curry_vec (f v)) in
               let sc := constr:(fst (Scope.inferNesting (Scope.Cookup.specialise cv))) in
               refine {| inTy   := fun sc' => forall w, Scope.allocation w sc'
                                                       -> subroutine _ w;
                         inLine := fun w => Scope.uncurry
                                              (st := sc)
                                              (cv%function w);
                         inSc   := sc;
                         verSub := _;
                         eqprf  := call _ _
                      |}.

(* TODO : Might be present in some standard library *)
Fixpoint distinctL [T] (l : list T)
  := let fix distH t l :=
         match l with
         | []         => True
         | (hd :: tl) => hd <> t /\ distH t tl
         end
     in
     match l with
     | []         => True
     | (hd :: tl) => distH hd tl /\ distinctL tl
     end.

Definition qualV [ts] (v : Variables.U ts) := sigT v.

Definition qualify [ts] [v : Variables.U ts] [ty] (x : v ty)
  : qualV v
  := existT _ ty x.

Definition distinctAll [ts] [sc : Scope.type ts]
           [v : Variables.U ts]
           (a : Scope.allocation v sc)
  : Prop
  := distinctL
       ((fix alltolist [ts] [sc : Scope.type ts]
             [v : Variables.U ts]
             (a : Scope.allocation v sc) :=
           match sc as sc0 return
                 Scope.allocation _ sc0 -> list _ with
           | []        => fun _  => []
           | ty :: tsc => fun an => (qualify (hlist.hd an))
                                    ::
                                    (alltolist (hlist.tl an))
           end a) ts sc v a).

Import Annotated.

Section ModProof.

  Variable tyD : typeDenote verse_type_system.

  (* We want to avoid symbolic expression explosion by leveraging the
  already packaged verified function calls we provide. Instead of
  actually computing/inlining the transformation of a function body,
  we replace it with an abstraction that esesntially clobbers all the
  variables passed to the function and assigns to them brand new
  symbolic values.

  We will later fix it so that the post-condition of the function is
  available on these new values. These will facilitate proofs of
  assertions at the call site.
  *)

  Definition dummyProc [v] [sc : Scope.type verse_type_system]
           (alloc : Scope.allocation v sc)
           (dummyvals : memory (tyD : Variables.U _) sc)
    : transformation sc tyD
    := fun _ => dummyvals.

  Variable sc : Scope.type verse_type_system.

  Let scv := HlistMachine.variable sc.

  (* We write our modular proof axiom for `modCode` instead of for a
     syntactic shape - block ++ proc call ++ block

     It just makes for cleaner code than massaging user code with a
     lot of rewrites with associativity-like theorems from the List
     module.

     Later we write a function that processes code to look for a
     `proc` and generate a `modCode` object from it. That opens up
     application of our meta theorem.
  *)

  Record preCall := { preB    : Annotated.code tyD scv;
                      procC   : vsubroutine tyD;
                      procAll : Scope.allocation scv (inSc procC) }.

  Definition modCode : Type := list preCall * Annotated.code tyD scv.

  Coercion getCode (mc : modCode) : list (Subroutine.statement tyD scv)
    := [ block
           (mapMconcat (fun pc =>
                        (preB pc
                           ++ inline_calls [inline (procC pc) (procAll pc)])) (fst mc) ++
            (snd mc)) ].

  Let Str := HlistMachine.state sc tyD.

  Local Definition PC (vf : vsubroutine tyD) : ann tyD (HlistMachine.variable (inSc vf))
    := match eqprf vf with
       | call f _ => postC (f _ (all_membership _))
       end.

  Let fSpec pc dummyVals := {| transform   := dummyProc (procAll pc) dummyVals;
                               guarantee   := srSnd (Annotated.statementDenote (annot (PC (procC pc))))
                            |}.

  Let lDummyProc pc dummyVals := transform (lift (fSpec pc dummyVals) (procAll pc) (procAll pc)).

  (* `spec` basically encapsulates the post-condition of the function
  for the abstraction we replace it with
   *)
  Let spec pc dummyVals := guaranteeOn (fSpec pc dummyVals).

  Fixpoint blackbox_vc_aux cpre mpre cs pb
    := match cs with
       | pc :: cst =>
           let mstep := Annotated.codeDenote (sc := sc) (preB pc) in
           distinctAll (procAll pc) /\
           forall dummyVals, blackbox_vc_aux (fun str => cpre str /\ spec pc dummyVals (gets (procAll pc) (srFst (mpre ** mstep) str)))
                                          (mpre ** mstep ** justInst
                                                (lDummyProc pc dummyVals))
                                          cst pb
       | []        =>   getProp cpre (mpre ** Annotated.codeDenote (sc := sc) (flatR pb))
       end.

  Definition blackbox_vc (mc : modCode)
    := blackbox_vc_aux (fun _ => True) ε (fst mc) (snd mc).

  Axiom modularize
    : forall mc, blackbox_vc mc
                 ->
                 getProp (fun _ => True) (Annotated.codeDenote (sc := sc) (inline_calls mc)).

End ModProof.

Arguments getCode [tyD sc].

(* We need a way to abstract a basic modular code block into a
   `modCode` struct so as to be able to use our modular proof. *)
Fixpoint splitAux [tyD]
  [sc : Scope.type verse_type_system]
  (l1 : Subroutine.code _ (HlistMachine.variable sc))
  (l2 : Annotated.code tyD (HlistMachine.variable sc))
  : modCode tyD sc
  := match l1 with
     | []       => ([], l2)
     | ac :: tl =>
         match ac with
         | inline f all  => let x := splitAux tl [] in
                            ({| preB := l2;
                                procC := f;
                                procAll := all |}
                               :: fst x
                              , snd x)
         | block b       => splitAux tl (l2 ++ b)
         end
     end.

Definition split [tyD]
           [sc : Scope.type verse_type_system]
           (l : Subroutine.code _ (HlistMachine.variable sc))
  : modCode tyD sc
  :=  splitAux l [].

(* Lastly we relate the abstraction created to the original object to
be able to use it at all *)
Lemma splitEq  [tyD] [sc : Scope.type verse_type_system]
      (l : Subroutine.code tyD (HlistMachine.variable sc))
  : inline_calls l = inline_calls (getCode (split l)).

Proof.
  (*Lemma*)
  assert (inline_nil : forall v, @inline_calls tyD v [] = []).
  (*Proof*)
  trivial.
  (*Qed*)

  (*Lemma*)
  assert (splitAuxCall : forall f all l1 (l2 : (Annotated.code tyD (HlistMachine.variable sc))),
             splitAux (inline f all :: l1) l2
             = ({| preB := l2;
                  procC := f;
                  procAll := all |}
                  :: fst (splitAux l1 [])
                 , snd (splitAux l1 []))).
  trivial.
  (*Qed*)

  (*Lemma*)
  assert (getCode_cons : forall (b : Annotated.code tyD (HlistMachine.variable sc)) f all cs pb,
             inline_calls (getCode ({| preB := b; procC := f; procAll := all |} :: cs, pb))
             = inline_calls (block (b ++ inline_calls [inline f all]) :: getCode (cs, pb))).
  intros.
  unfold getCode.
  simpl.
  rewrite mapMconcat_cons.
  simpl.
  unfold binop.
  unfold list_append_binop.
  rewrite inline_instructions.
  unfold inline_calls.
  unfold map.
  unfold inline_call at 3 5.
  unfold concat.
  repeat rewrite app_nil_r.
  now repeat rewrite app_assoc.
  (*Qed*)

  enough (splitAuxEq : forall l1 (l2 : Annotated.code tyD (HlistMachine.variable sc)),
             l2 ++ inline_calls l1 = inline_calls (splitAux l1 l2)).
  apply (splitAuxEq _ []).

  induction l1.
  * intro l2.
    unfold getCode.
    rewrite inline_instructions.
    now rewrite app_nil_r.
  * intro l2.
    induction a.
    + unfold inline_calls at 1.
      rewrite map_cons.
      simpl.
      rewrite app_assoc.
      now rewrite IHl1.
    + rewrite splitAuxCall.
      rewrite getCode_cons.
      unfold inline_calls.
      repeat rewrite map_cons.
      unfold inline_call at 3.
      unfold map at 2.
      pose inline_instructions.
      unfold inline_calls in e, IHl1.
      repeat rewrite concat_cons at 1.
      rewrite <- surjective_pairing.
      rewrite <- IHl1.
      now repeat rewrite <- app_assoc.
Qed.

(* Extracting Prop object from annotated code *)


Require Import Verse.Scope.
Section CodeGen.

  Variable sc : Scope.type verse_type_system.

  Variable tyD : typeDenote verse_type_system.

  Variable ac : forall v, Scope.scoped v sc (Repeat (Subroutine.statement tyD v)).

  (* TODO: This is really a bad name particularly because it is being used outside (is it ?). *)
  Definition cp
    := Annotated.codeDenote (sc := sc) (inline_calls (flatR (HlistMachine.specialise sc ac))).

  Definition vc := getProp (fun _ => True) cp.

End CodeGen.

Global Hint Unfold vc : Wrapper.
Global Hint Unfold cp  : Wrapper.

Arguments cp sc [tyD].
Arguments getProp [sc tyD].
Arguments vc sc [tyD].

Ltac vc_gen func
  := (let cv := constr:(fun v => Scope.curry_vec (func v)) in
      let level0 := constr:(Scope.Cookup.specialise cv) in
      let level0break := (eval hnf in (Scope.inferNesting level0)) in
      let pvs := constr:(fst level0break) in
      let level1 := constr:(snd level0break) in
      let lvs := (eval hnf in (fst (Scope.inferNesting level1))) in
      exact (vc (pvs ++ lvs)%list cv)).

Module Tactics.
  (* For simple subroutine proofs, with post-conditions simply giving
  symbolic executions of the subroutine, this effectively restores the
  usual full symbolic execution *)
  Ltac inline :=   repeat match goal with
                          | _ : ?a = _ |- _ => try (subst a)
                          end.
End Tactics.

Export Tactics.