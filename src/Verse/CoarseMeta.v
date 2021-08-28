Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.
Require Import Verse.Ast.
Require Import Verse.AnnotatedCode.
Require Import Verse.AbstractMachine.
Require Verse.Scope.
Require Import Verse.ScopeStore.
Require Import Verse.Language.Pretty.
Require Import Verse.Monoid.

Require Import List.
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

Section Coarse.

  Variable tyD : typeDenote verse_type_system.
  Variable Rels : forall (ty : typeOf verse_type_system direct),
      Rel tyD ty -> Prop
  .

  Variable ty : typeOf verse_type_system direct.

  Fixpoint dummyProc [n v] (alloc : Scope.allocation v (const (existT _ _ ty) n))
           (dummyvals : Vector.t (Types.const ty) n)
           {struct n}
    : AnnotatedCode tyD Rels v
    := (match n as n0
             return Scope.allocation v (const _ n0) -> Vector.t (Types.const ty) n0 -> _
       with
       | 0   => fun _ _ => []
       | S m => fun allS dumS =>
                  CODE [ assignStmt (var (fst allS)) (fst allS : v _ _)  ]%verse
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

  Variable n  : nat.

  Local Definition sc := const (existT _ _ ty) n.
  Definition v := Scope.scopeVar sc.


  Axiom modularProof
    : forall (apre : AnnotatedCode tyD Rels v)
             (f : forall [w], Scope.allocation w sc
                              -> AnnotatedCode tyD Rels w)
             (alloc : Scope.allocation v sc)
             (apost : AnnotatedCode tyD Rels v)

             (procP : tpt sc (fun w => Scope.curryScope (@f w) ))
             (distinct : distinctAll alloc)
             (modP : forall dVals,
                 let preP := interpret (denote apre) in
                 let dumP := interpret (denote (dummyProc alloc dVals)) in
                 let procP := snd (interpret (denote (f alloc))
                                             (scopeStore _ _)) in
                 let postP := (interpret (denote apost)) in
                 let cp := preP ** dumP ** postP in
                 getProp procP cp),

      getProp (fun _ => True) (interpret (denote (apre ++ (proc _ _ _ _ _ f alloc) :: apost)))%list.

End Coarse.

(*
pre-block   ---  state -> state, assertion  (* assertion includes d = OLD e *)

proc a b c  ---  state -> state, assertion  (* assertion should technically specify the proc *)
        replaced by

a = va; b = vb; c = vc  --- and provide assertion on va vb vc as hypothesis to the rest

post-block  ---  state -> state, assertion


*)
(* forall (- va vb vc -), a = va; b = vb; c = vc; *)
