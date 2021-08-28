Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Ast.
Require Import Verse.AnnotatedCode.
Require Import Verse.AbstractMachine.
Require Verse.Scope.
Require Import Verse.ScopeStore.
Require Import Verse.Language.Pretty.
Require Import Verse.Monoid.
Require Import Verse.Machine.BitVector.

Require Import Verse.Monoid.PList.
Import ListNotations.

Require Import Vector.

Fixpoint distinctL [T] (l : list T)
  := let fix distH t l :=
         match l with
         | []         => True
         | (hd :: tl) => t <> hd /\ hd <> t /\ distH t tl
         end
     in
     match l with
     | []         => True
     | (hd :: tl) => distH hd tl /\ distinctL tl
     end.

Definition qualV [ts] (v : Variables.U ts) := sigT (qualified v).

Definition qualify [ts] [v : Variables.U ts] [k ty] (x : v k ty)
  : qualV v
  := existT _ (existT _ _ ty) x.

Definition distinctAll [ts n] [sc : Scope.type ts n]
           [v : Variables.U ts]
           (a : Scope.allocation v sc)
  : Prop
  := distinctL
       ((fix alltolist [ts n] [sc : Scope.type ts n]
             [v : Variables.U ts]
             (a : Scope.allocation v sc) :=
           match n as n0 return forall (sc0 : Scope.type ts n0),
               Scope.allocation _ sc0 -> list _ with
           | 0   => fun _ _    => []
           | S n => fun scn an => (qualify (fst an))
                                    ::
                                    (alltolist (snd an))
           end sc a) ts n sc v a).

Module Prodn.

  Fixpoint t T n : Type
    := match n with
       | 0   => Datatypes.unit
       | S n => (T * t T n)%type
       end.

End Prodn.

Section Coarse.

  Variable tyD : typeDenote verse_type_system.
  Variable Rels : forall (ty : typeOf verse_type_system direct),
      Rel tyD ty -> Prop
  .

  Fixpoint dummyProc [n v ty] (alloc : Scope.allocation v (const (existT _ _ ty) n))
           (dummyvals : Prodn.t (Types.const ty) n)
           {struct n}
    : AnnotatedCode tyD Rels v
    := (match n as n0
             return Scope.allocation v (const _ n0) -> Prodn.t (Types.const ty) n0 -> _
       with
       | 0   => fun _ _ => []
       | S m => fun allS dumS =>
                  CODE [ assignStmt (var (fst allS)) (fst dumS)  ]%verse
                        ++
                        dummyProc (snd allS) (snd dumS)
       end alloc dummyvals).

(* This generic version doesn't work because you need the variables to
   be of `kind` direct.


  Fixpoint dummyproc n (sc : Scope.type verse_type_system n)
           (alloc : Scope.allocation v sc)
           (dummyvals : Scope.allocation (typeTrans tyD) sc)
           {struct n}
    : AnnotatedCode tyD Rels v
    := (match n as n0 return
              forall sc0 : Scope.type _ n0,
                Scope.allocation v sc0 ->
                Scope.allocation (typeTrans tyD) sc0 ->
                _
        with
        | 0   => fun _ _ _ => []
        | S m => fun scS allocS dumS =>
                   CODE [ assignStmt (var (fst allocS)) (fst allocS : v _ _)  ]%verse
                        ++
                        dummyproc m (Vector.tl scS)
                        (snd allocS)
                        (snd dumS)
        end sc alloc dummyvals).
 *)


  Variable m : nat.
  Variable sc : Scope.type verse_type_system m.

  Let scv := Scope.scopeVar sc.

  Record modCode := { preB   : AnnotatedCode tyD Rels scv;

                      procN  : nat;
                      procTy : verse_type_system direct;

                      procC  : specifiedC tyD Rels procN procTy;

                      procAll : Scope.allocation scv (Scope.const procN procTy);

                      postB  : AnnotatedCode tyD Rels scv
                    }.

  Coercion getCode (mc : modCode) : AnnotatedCode tyD Rels scv
    := preB mc ++ (proc (procC mc) (procAll mc)) :: (postB mc)
  .

  Definition specifiedCDenote [tyD Rels n ty] (f : specifiedC tyD Rels n ty)
    := let (pre, bl, post) := Scope.fillScoped
                                (fun w =>
                                   Scope.curryScope
                                     (fun all => @f w all))
       in getProp (fun str =>
                     VPropDenote pre (scopeStore _ _)
                                 {| oldAndNew := (str, str) |})
                  (interpret (denote (bl ++ [ annot post ]))).

(* TODO : Make a big axiom section and make all the parameters and
          let's section variables and definitions *)
  Axiom modularProof
    : forall cpre
             (apre : AnnotatedCode tyD Rels scv)
             n ty
             (f : specifiedC tyD Rels n ty)
             (alloc : Scope.allocation scv (Scope.const n ty))
             (apost : AnnotatedCode tyD Rels scv)

             (distinct : distinctAll alloc)

             (modP : forall dVals,
                 let (preF, blF, postF) := f _ alloc in
                 let preI := interpret (denote apre) in
                 let dumI := interpret (denote
                                          (dummyProc alloc dVals
                                               ++
                                           [annot postF]
                                       )) in
                 let procP := fun str =>
                                snd ((justInst
                                       (fun st => fst (preI st))
                                    **
(* TODO                                (fun st => Semantics.inliner _ _
                                                                 store_semantics
                                                                 dumI)*)
                                    (fun st => (fst (dumI st),
                                                fun stp =>
                                                  (snd (dumI st)) (snd stp, snd stp)))) (scopeStore _ _))
                                    (str, str)
                 in
                 getProp (fun str => cpre str /\ procP str)
                         (interpret (denote
                                       (apre
                                          ++ [annot preF]
                                          ++ dummyProc alloc dVals
                                          ++ apost))))

             (procP : specifiedCDenote f)
    ,
      getProp cpre (interpret
                      (denote
                         (getCode
                            (Build_modCode apre
                                           _
                                           _
                                           f
                                           alloc
                                           apost)))).

End Coarse.

(*
pre-block   ---  state -> state, assertion  (* assertion includes d = OLD e *)

proc a b c  ---  state -> state, assertion  (* assertion should technically specify the proc *)
        replaced by

a = va; b = vb; c = vc  --- and provide assertion on va vb vc as hypothesis to the rest

post-block  ---  state -> state, assertion
Fixpoint getProc [tyD Rels n]
         [sc : Scope.type verse_type_system n]
         (l1 l2 : AnnotatedCode _ Rels (Scope.scopeVar sc)) {struct l2}
  : option (modCode tyD Rels n sc)
  := match l2 with
     | []       => None
     | ac :: tl => match ac with
                   | proc f all => Some {| preB    := l1;
                                           procC   := f;
                                           procAll := all;
                                           postB   := tl
                                        |}
                   | _          => getProc (l1 ++ [ac]) tl
                   end
     end.

Definition split [tyD Rels n]
           [sc : Scope.type verse_type_system n]
           (l : AnnotatedCode _ Rels (Scope.scopeVar sc))
  : option (modCode tyD Rels n sc)
  :=  getProc [] l.

Lemma splitEq  [tyD Rels n] [sc : Scope.type verse_type_system n]
      (l : AnnotatedCode tyD Rels (Scope.scopeVar sc))
  : match split l with
    | Some mc => l = mc
    | None    => True (* TODO : could be eq_refl l *)
    end.
Proof.

  assert (forall l2 l1 : AnnotatedCode tyD Rels (Scope.scopeVar sc),
             match getProc l1 l2 with
             | Some mc => l1 ++ l2 = (mc : AnnotatedCode _ _ _)
             | None    => True
             end).

  induction l2.
  * easy.
  * induction a.
  + simpl.
    assert (forall T t (l : list T), t :: l = [t] ++ l).
    easy.
    rewrite (H _ (instruct s) l2).
    intro.
    rewrite (app_assoc l1 [instruct s] l2).
    apply IHl2.
  + simpl.
    now unfold getCode.
  + simpl.
    assert (forall T t (l : list T), t :: l = [t] ++ l).
    easy.
    rewrite (H _ (annot v) l2).
    intro.
    rewrite (app_assoc l1 [annot v] l2).
    apply IHl2.
    * unfold split.
      apply H.
Qed.

Fixpoint lamn T n
  : (Prodn.t T n -> Type) -> Type
  := match n as n0
           return (Prodn.t T n0 -> Type) -> Type
     with
     | 0   => fun f => forall t, f t
     | S n => fun f => forall t, lamn _ n (fun x => f (t, x))
     end.

Lemma forallprod T n f
  : lamn T n f
    ->
    forall x : Prodn.t T n, f x.
  induction n.
  easy.
  intros.
  pose (IHn _ (X (fst x)) (snd x)).
  rewrite surjective_pairing.
  exact f0.
Qed.


Ltac breakDVals :=
  let st := fresh "st" in
  match goal with
  | |- forall _, _ => intro st; simpl in st; revert st
  end;
  let nsc := fresh "nsc" in
  (match goal with
   | |- forall _ : ?t, _  =>
     let nsc := prodsize t in
     refine (forallprod _
                        nsc
                        _
                        _

            )
   end;
   unfold lamn; intros).

Ltac modProof :=
  let rec inner := first [ match goal with
                           | |- context [getProp _ (interpret (denote ?l))]
                             => rewrite (splitEq l); apply modularProof;
                                [> unfold distinctAll; simpl; easy
                                | let dv := fresh "dv" in
                                  intro dv; simpl in dv;
                                  revert dv; breakDVals;
                                  simpl; inner
                                | (* unfold specifiedCDenote;
                                     simpl; inner *)

                                (* While the above tactic would solve
                                the functions too, we would like to
                                employ an external lemma or so here to
                                really modularize the function proofs

                                simpl

                                ]
                           end
                         | simplify ]
  in inner.

Ltac mrealize := unwrap; modProof.
