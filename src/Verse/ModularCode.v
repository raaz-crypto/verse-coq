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

Require Import Verse.AbstractMachine.
Require Import Verse.AnnotatedCode.
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

Section Call.

  Context [tyD : typeDenote verse_type_system]
          [ v  : VariableT ].

  Record specBlock w := { block   : lines tyD w;
                          postC   : ann tyD w    }.

  Arguments block [w].
  Arguments postC [w].

  Local Definition tyd ty := typeTrans tyD (projT2 ty).

  Local Definition sub (sc : Scope.type verse_type_system)
    := subroutine tyd sc sc.

  Definition func sc
    := forall w, Scope.allocation w sc
                 -> specBlock w.


  (* Specifying the type of `funSub` explicitly as `sub (scp fc)` doesn't work.
     Even if we use `HlistMachine.tyd` instead of `tyd` in the definition of sub! *)
  Definition funSub sc (fc : func sc)
    := let (bl, pc)   := fc (memV sc) (all_membership sc) in
       {| requirement := fun _ => True;
          transform   := srFst (linesDenote bl);
          guarantee   := srSnd (lineDenote (annot pc))
       |}.

  Inductive equiv : forall [T], T -> forall [sc], vsubroutine tyd sc sc -> Type :=
  | call : forall [sc] (fc : func sc)
                  (vc : VC (funSub sc fc)), equiv fc (exist _ _ vc).

  Record verFun := { inTy   : Scope.type verse_type_system -> Type;
                     inSc   : Scope.type verse_type_system;
                     inLine : inTy inSc;
                     vsub   : vsubroutine tyd inSc inSc;
                     eqprf  : @equiv _ inLine inSc vsub }.

  Inductive modular :=
  | instruction   : line tyD v -> modular
  | inline        : forall vfun, Scope.allocation v (inSc vfun) -> modular.

  (* We consider the default interpretation of a `call` to be an
  inlining of the text of the function while stripping it of its
  annotations. We do this to avoid inadvertant errors and confusion
  arising from the intended meaning of `INIT` values in annotations
  inside functions.
   *)

  Definition stripAnn [v] (ls : lines tyD v)
    := concat (map (fun l => match l with
                             | inst _ as l0 => [ l0 ]
                             | _            => []
                             end)
                 ls).

  Definition inline_call (a : modular) : lines tyD v
    := match a with
       | instruction i => [i]
       | inline sl all => match eqprf sl with
                          | call fc vc => fun all0 => stripAnn (block (fc v all0))
                          end all
       end.

  Definition inline_calls := mapMconcat inline_call.

  Lemma inline_instructions (ls : lines tyD v)
    : inline_calls (map instruction ls) = ls.
  Proof.
    induction ls.
    * trivial.
    * unfold inline_calls.
      rewrite map_cons, mapMconcat_cons.
      fold inline_calls.
      now rewrite IHls.
  Qed.

End Call.

Arguments postC [tyD w].
Arguments specBlock tyD w : clear implicits.
Arguments modular tyD v : clear implicits.
Arguments verFun tyD : clear implicits.

Require Import Verse.Language.Pretty.
Require Verse.Ast.

Module ModularCode.

  #[export] Instance statement_modular tyD (v : VariableT)
    : AST_maps (list (Ast.statement v)) (modular tyD v)
    := {| CODE := map (Basics.compose (@instruction _ _) (@inst _ _)) |}.

  #[export] Instance annot_modular tyD (v : VariableT) : AST_maps (ann tyD v) (modular tyD v)
    := {| CODE := fun an => [ instruction (annot an) ] |}.

End ModularCode.

Notation "'CALL' f 'WITH' a" := (inline f a) (at level 60).

Notation "F 'DOES' Post" := ({| block := F;
                                postC := fun _ : StoreP (Str _ _) => Post |})
                              (at level 60).

Ltac Pack f :=     refine (let sc := fst (Scope.inferNesting (Scope.Cookup.specialise f)) in
                       {| inTy   := fun sc => forall w, Scope.allocation w sc
                                              -> specBlock _ w;
                          inLine := fun w => Scope.uncurry
                                            (st := sc)
                                            (f%function w);
                          inSc   := sc;
                          vsub   := _;
                          eqprf  := call _ _ |}).

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

Import AnnotatedCode.

Section ModProof.

  Variable tyD : typeDenote verse_type_system.

  Let tyd ty := typeTrans tyD (projT2 ty).

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
           (dummyvals : memory tyd sc)
    : transformation sc tyD
    := fun _ => dummyvals.

  Variable sc : Scope.type verse_type_system.

  Let scv := memV sc.

  (* We write our modular proof axiom for `modCode` instead of for a
     syntactic shape - block ++ proc call ++ block

     It just makes for cleaner code than massaging user code with a
     lot of rewrites with associativity-like theorems from the List
     module.

     Later we write a function that processes code to look for a
     `proc` and generate a `modCode` object from it. That opens up
     application of our meta theorem.
  *)

  Record preCall := { preB   : lines tyD scv;
                      procC   : verFun tyD;
                      procAll : Scope.allocation scv (inSc procC) }.

  Definition modCode : Type := list preCall * lines tyD scv.

  Coercion getCode (mc : modCode) : list (modular tyD scv)
    := map (@instruction _ _ )
         (mapMconcat (fun pc =>
                        (preB pc
                           ++ inline_calls [inline (procC pc) (procAll pc)])) (fst mc)
            ++ snd mc).

  Let Str := str (State := HlistMem sc tyD).

  Local Definition PC (vf : verFun tyD) : ann tyD (memV (inSc vf))
    := match eqprf vf with
       | call f _ => postC (f _ (all_membership _))
       end.

  Let fSpec pc dummyVals := {| requirement := fun _ => True;
                              transform   := dummyProc (procAll pc) dummyVals;
                              guarantee   := srSnd (lineDenote (annot (PC (procC pc))))
                            |}.

  Let lDummyProc pc dummyVals := transform (lift (fSpec pc dummyVals) (procAll pc) (procAll pc)).

  (* `spec` basically encapsulates the post-condition of the function
  for the abstraction we replace it with
   *)
  Let spec pc dummyVals := VCi (fSpec pc dummyVals).

  Fixpoint modProofAux cpre mpre cs pb
    := match cs with
       | pc :: cst =>
           let mstep := linesDenote (preB pc) in
           distinctAll (procAll pc) /\
           forall dummyVals, modProofAux (fun str => cpre str /\ spec pc dummyVals (gets (procAll pc) (srFst (mpre ** mstep) str)))
                                          (mpre ** mstep ** justInst (H := HlistMem _ _)
                                                (lDummyProc pc dummyVals))
                                          cst pb
       | []        =>   getProp cpre (mpre ** linesDenote pb)
       end.

  Definition modularProof (mc : modCode)
    := modProofAux (fun _ => True) ε (fst mc) (snd mc).

  Axiom modularize
    : forall mc, modularProof mc
                 ->
                   getProp (fun _ => True) (linesDenote (inline_calls mc)).

End ModProof.

Arguments getCode [tyD sc].

(* We need a way to abstract a basic modular code block into a
   `modCode` struct so as to be able to use our modular proof. *)
Fixpoint splitAux [tyD]
  [sc : Scope.type verse_type_system]
  (l1 : list (modular _ (memV sc)))
  (l2 : lines tyD (memV sc))
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
         | instruction i => splitAux tl (l2 ++ [i])
         end
     end.

Definition split [tyD]
           [sc : Scope.type verse_type_system]
           (l : list (modular _ (memV sc)))
  : modCode tyD sc
  :=  splitAux l [].

(* Lastly we relate the abstraction created to the original object to
be able to use it at all *)
Lemma splitEq  [tyD] [sc : Scope.type verse_type_system]
      (l : list (modular tyD (memV sc)))
  : inline_calls l = inline_calls (getCode (split l)).

Proof.
  (*Lemma*)
  assert (inline_inst : forall v (l : lines tyD v),
             inline_calls (map (@instruction tyD v) l) = l).
  (*Proof*)
  intros v0 l0.
  induction l0.
    easy.

    simpl. unfold inline_calls.
    rewrite mapMconcat_cons.
    simpl.
    rewrite <- IHl0 at 2.
    trivial.
  (*Qed*)

  (*Lemma*)
  assert (inline_nil : forall v, @inline_calls tyD v [] = []).
  (*Proof*)
  trivial.
  (*Qed*)

  (*Lemma*)
  assert (splitAuxCall : forall f all l1 (l2 : lines tyD (memV sc)),
             splitAux (inline f all :: l1) l2
             = ({| preB := l2;
                  procC := f;
                  procAll := all |}
                  :: fst (splitAux l1 [])
                 , snd (splitAux l1 []))).
  trivial.
  (*Qed*)

  (*Lemma*)
  assert (getCode_cons : forall (b : lines tyD (memV sc)) f all cs pb,
             getCode ({| preB := b; procC := f; procAll := all |} :: cs, pb)
             = map (@instruction _ _) (b ++ inline_calls [inline f all]) ++ getCode (cs, pb)).
  intros.
  unfold getCode.
  simpl.
  rewrite mapMconcat_cons.
  simpl.
  unfold binop.
  unfold list_append_binop.
  repeat rewrite map_app.
  now repeat rewrite app_assoc.
  (*Qed*)

  enough (splitAuxEq : forall l1 (l2 : lines tyD (memV sc)),
             l2 ++ inline_calls l1 = inline_calls (splitAux l1 l2)).
  apply (splitAuxEq _ []).

  induction l1.
  * intro l2.
    unfold getCode.
    rewrite inline_inst.
    now rewrite app_nil_r.
  * intro l2.
    induction a.
    + unfold inline_calls.
      rewrite mapMconcat_cons.
      unfold binop.
      rewrite app_assoc.
      now rewrite IHl1.
    + rewrite splitAuxCall.
      rewrite getCode_cons.
      unfold inline_calls.
      rewrite mapMconcat_cons.
      rewrite mapMconcat_app.
      unfold inline_calls in inline_inst, IHl1.
      rewrite inline_inst.
      unfold binop, list_append_binop.
      repeat rewrite app_assoc.
      f_equal.
      rewrite <- surjective_pairing.
      rewrite <- IHl1.
      apply app_nil_l.
Qed.

(* Extracting Prop object from annotated code *)

Require Import Verse.Scope.

Section CodeGen.

  Variable sc : Scope.type verse_type_system.

  Variable tyD : typeDenote verse_type_system.

  Variable ac : forall v, Scope.scoped v sc (list (modular tyD v)).

  Definition cp := linesDenote (inline_calls (fillMemV ac)).

  Definition tpt := getProp (fun _ => True) cp.

End CodeGen.

Global Hint Unfold tpt : Wrapper.
Global Hint Unfold cp  : Wrapper.

Arguments cp sc [tyD].
Arguments getProp [sc tyD].
Arguments tpt sc [tyD].

Ltac getProp func
  := (let cv := constr:(fun v => Scope.curry_vec (func v)) in
      let level0 := constr:(Scope.Cookup.specialise cv) in
      let level0break := (eval hnf in (Scope.inferNesting level0)) in
      let pvs := constr:(fst level0break) in
      let level1 := constr:(snd level0break) in
      let lvs := (eval hnf in (fst (Scope.inferNesting level1))) in
      exact (tpt (pvs ++ lvs)%list cv)).
