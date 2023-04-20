Require Import Verse.TypeSystem.
Require Import Verse.Target.
Require Import Verse.Target.C.CodeGen.
Require Import Verse.Utils.hlist.

Module Compile := Target.CodeGen (C.CodeGen.Config).
Definition variables := Compile.variables.


(** * Auto allocation.

Since C can be seen as a machine with infinitely many registers, we
give an auto allocation for parameters and local variables. The down
side of this process is that we end up with meaningless variable names
in the generated code.


 *)

Require Import Verse.Target.C.Ast.
Import Expr.
Require Verse.Scope.
Require Import List.
Import List.ListNotations.

(* begin hide *)
Module Internals.

  Program Definition mkVar (alk : nat) (ty : sigT type) : variables ty
    := match projT2 ty as ty0 return variables of type ty0 with
       | uint8_t  as ty0  => cvar2exp ((cVar of type ty0) alk)
       | uint16_t as ty0   => cvar2exp ((cVar of type ty0) alk)
       | uint32_t as ty0  => cvar2exp ((cVar of type ty0) alk)
       | uint64_t as ty0  => cvar2exp ((cVar of type ty0) alk)
       | (array sz t) as ty0  => cvar2exp ((cVar of type ty0) alk)
       | (ptrToArray sz t) as ty0 => let ptrVar := @bPtr sz t in
                           let ctrVar := cTr in
                           (cvar2exp ptrVar, cvar2exp ctrVar)
       end.

  Definition mkQVar (alk : nat) s : variables s :=
    mkVar alk s.

  Fixpoint calloc (alk : nat) (st :  Scope.type C.Ast.c_type_system)
    : Scope.allocation variables st * nat
    := match st as st0 return Scope.allocation variables st0 * nat with
         | [] => ([]%hlist, alk)
         | qty  :: qts
           => let (xs, used) := calloc (S alk) qts  in
             ((mkQVar alk qty :: xs)%hlist, used)
         end.

End Internals.
Require Import Verse.
Require Export Verse.Error.

(* end hide *)

Import Scope.

Ltac Function name func
  := ( let cfunc := constr:(Scope.curry_vec func) in
       let level0 := constr:(Scope.Cookup.specialise cfunc) in
       let level0break := (eval hnf in (inferNesting level0)) in
       let pvs := constr:(fst level0break) in
       let level1 := constr:(snd level0break) in
       let lvs := (eval hnf in (fst (inferNesting level1))) in
       let cpvs := (eval hnf in (recover (Compile.targetTypes pvs))) in
       let clvs := (eval hnf in (recover (Compile.targetTypes lvs))) in
       exact ((fun pfpvt pflvt =>
                 let (pA,n0) := Internals.calloc 0 cpvs in
                 let (lA,_) := Internals.calloc n0 clvs in
                 (Compile.function name pvs lvs
                                   cpvs clvs
                                   pfpvt pflvt
                                   pA lA cfunc)
                   (** TODO: This can be a normal function application if
                             inferNesting carries around correctness proofs
                    *)

              ) (*(recover (Compile.targetTypes pvs))
                (recover (Compile.targetTypes lvs))*)
                eq_refl eq_refl)
     ).

Ltac Iterator name memty ifunc
  := ( let cifunc := constr:(Scope.curry_vec ifunc) in
       let memtyTgt
           := constr:(recover (TypeSystem.Types.compile Compile.Config.typeCompiler memty)) in
       let level0       := constr:(Cookup.specialise cifunc) in
       let level0break  := (eval hnf in (inferNesting level0)) in
       let pvs          := constr:(fst level0break) in
       let level1       := constr:(snd level0break) in
       let lvs := (eval hnf in (fst (inferNesting level1))) in
       let pvt := constr:(recover (Compile.targetTypes pvs)) in
       let lvt := constr:(recover (Compile.targetTypes lvs)) in
       exact ((fun pfpvt pflvt =>
                 let (pA,n0) := Internals.calloc 0 pvt in
                 let (lA,n1) := Internals.calloc n0 lvt in
                 let streamVar := Internals.mkVar n1 of type (Compile.Config.streamOf memtyTgt) in
                 Compile.iterativeFunction name memty
                                           pvs lvs
                                           memtyTgt eq_refl
                                           streamVar
                                           pvt     lvt
                                           pfpvt   pflvt
                                           pA      lA
             ) eq_refl eq_refl cifunc
     )).

Require Export Verse.Target.C.Ast.
Require Export Verse.Target.C.Pretty.
