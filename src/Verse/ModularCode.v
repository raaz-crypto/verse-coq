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

  Instance statement_modular tyD (v : VariableT)
    : AST_maps (list (Ast.statement v)) (modular tyD v)
    := {| CODE := map (Basics.compose (@instruction _ _) (@inst _ _)) |}.

  Instance annot_modular tyD (v : VariableT) : AST_maps (ann tyD v) (modular tyD v)
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

  Record modCode := { preB   : list (modular tyD scv);

                      procC  : verFun tyD;

                      procAll : Scope.allocation scv (inSc procC);

                      postB  : list (modular tyD scv)
                    }.

  Coercion getCode (mc : modCode) : list (modular tyD scv)
    := preB mc
            ++ map (@instruction _ _)
                   (inline_call (inline (procC mc) (procAll mc)))
            ++ postB mc.

  Let Str := str (State := HlistMem sc tyD).

  Local Definition pc (vf : verFun tyD) : ann tyD (memV (inSc vf))
    := match eqprf vf with
       | call f _ => postC (f _ (all_membership _))
       end.

  (* We will be providing a way to prove the de facto verification
     condition of annotated code with calls -

     `getProp (linesDenote (inline_calls <modCode>))`

     Since we do this one call at a time, successive rewrites would
     prepend both a precondition and an already computed
     transformation/intruction to the next such `getProp`.
   *)

  Variable cpre : Str -> Prop. (* precondition from previous lemma applications *)
  Variable dpre : mline scv tyD (HlistMem _ _). (* semantic machine line corresponding to previous lemma applications *)
  Variable f : verFun tyD.
  Variable alloc : Scope.allocation scv (inSc f).
  Variable preb postb : list (modular tyD scv).

  Let fSpec dummyVals := {| requirement := fun _ => True;
                            transform   := dummyProc alloc dummyVals;
                            guarantee   := srSnd (lineDenote (annot (pc f)))
                         |}.

  Let lDummyProc dummyVals := transform (lift (fSpec dummyVals) alloc alloc).

  (* `spec` basically encapsulates the post-condition of the function
  for the abstraction we replace it with
  *)
  Let spec dummyVals i := VCi (fSpec dummyVals) i.


  Axiom modularProof
    :forall (linear : distinctAll alloc)
            (modP : forall dummyVals,
                let mpre := linesDenote (inline_calls preb) in
                getProp (fun str => cpre str /\ spec dummyVals (gets alloc (srFst (dpre ** mpre) str)))
                        ((mpre
                           ** justInst (H := HlistMem _ _) (lDummyProc dummyVals))
                           ** linesDenote (inline_calls postb)))

    ,
      getProp cpre (dpre ** linesDenote (inline_calls ({| preB := preb;
                                                         procC := f;
                                                         procAll := alloc;
                                                         postB := postb |}))).

End ModProof.

Arguments getCode [tyD sc].

(* We need a way to abstract a basic modular code block into a
`modCode` struct so as to be able to use our modular proof. *)

Fixpoint splitAux [tyD]
         [sc : Scope.type verse_type_system]
         (l1 l2 : list (modular _ (memV sc))) {struct l2}
  : option (modCode tyD sc)
  := match l2 with
     | []       => None
     | ac :: tl => match ac with
                   | inline f all => Some {| preB    := l1;
                                             procC   := f;
                                             procAll := all;
                                             postB   := tl
                                          |}
                   | _            => splitAux (l1 ++ [ac]) tl
                   end
     end.

Definition split [tyD]
           [sc : Scope.type verse_type_system]
           (l : list (modular _ (memV sc)))
  : option (modCode tyD sc)
  :=  splitAux [] l.

(* Lastly we relate the abstraction created to the original object to
be able to use it at all *)
Lemma splitEq  [tyD] [sc : Scope.type verse_type_system]
      (l : list (modular tyD (memV sc)))
  : match split l with
    | Some mc => inline_calls l = inline_calls (getCode mc)
    | None    => True (* TODO : could be eq_refl l *)
    end.
Proof.
  assert (cons_app : forall T t (l : list T), t :: l = [t] ++ l).
  easy.
  unfold split.
  enough (H : forall l2 l1 : list (modular tyD (memV sc)),
             match splitAux l1 l2 with
             | Some mc => inline_calls (l1 ++ l2) = inline_calls (mc : list (modular _ _))
             | None    => True
             end).
  apply H.

  induction l2.
  * easy.
  * induction a.
  + rewrite (cons_app _ (instruction l0) l2).
    intro.
    rewrite (app_assoc l1 [instruction l0] l2).
    apply IHl2.
  + unfold getCode.
    simpl.
    rewrite (cons_app _ _ l2).
    unfold inline_calls.
    intro.
    repeat rewrite mapMconcat_app.
    apply f_equal.
    apply (f_equal (fun ls => ls ** mapMconcat _ _)).
    pose (ii := inline_instructions).
    unfold inline_calls in ii.
    now rewrite ii.
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
