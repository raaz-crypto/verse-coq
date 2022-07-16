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

Require Import Verse.Abstract.Machine.
Require Import Verse.AbstractMachine.
Require Import Verse.AnnotatedCode.
Require Import Verse.HlistMachine.
Require Import Verse.Language.Types.
Require Import Verse.Monoid.
Require Verse.Scope.
Require Import Verse.TypeSystem.
Require Import Verse.Utils.hlist.

Require Import PList.
Import ListNotations.


Section Call.

  Context [tyD : typeDenote verse_type_system]
          [v   : Variables.U verse_type_system].

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
    := let (bl, pc)   := (fc) (memV (sc)) (all_membership (sc)) in
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

  Definition stripAnn (ls : lines tyD v)
    := concat (map (fun l => match l with
                             | inst _ as l0 => [ l0 ]
                             | _            => []
                             end)
                 ls).

  Definition inline_text (la : list modular) : lines tyD v
    := concat (map (fun a => match a with
                             | instruction i => [i]
                             | inline sl all => match eqprf sl with
                                                | call fc vc => fun all0 => stripAnn (block (fc v all0))
                                                end all
                             end)
                 la).

End Call.

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
                                postC := fun _ : StoreP (Str _ _) => Post (*((fun (_ : StoreP str) => Post) : StoreP str -> Prop) : Pair str -> Prop*) |})
                              (at level 60).
