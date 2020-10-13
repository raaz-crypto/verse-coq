Require Import Verse.Target.
Require Import Verse.Target.C.CodeGen.

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
Require Vector.
Import Vector.VectorNotations.

(* begin hide *)
Module Internals.

  Definition mkVar (alk : nat) {k} (ty : type k) : variables k ty
    := match ty as ty0 in type k0 return variables k0 ty0 with
       | uint8_t    => cvar2exp (cVar uint8_t alk)
       | uint16_t   => cvar2exp (cVar uint16_t alk)
       | uint32_t   => cvar2exp (cVar uint32_t alk)
       | uint64_t   => cvar2exp (cVar uint64_t alk)
       | array sz t  => cvar2exp (cVar (array sz t) alk)
       | ptrToArray sz t => let ptrVar := @bPtr sz t in
                           let ctrVar := cTr in
                           (cvar2exp ptrVar, cvar2exp ctrVar)
       end.

  Definition mkQVar (alk : nat) s : TypeSystem.qualified variables s :=
    mkVar alk (projT2 s).

  Fixpoint calloc (alk : nat) {n} (st :  Scope.type C.Ast.c_type_system n)
    : Scope.allocation variables st * nat
    := match st as st0 return Scope.allocation variables st0 * nat with
         | [] => (tt, alk)
         | qty  :: qts
           => let (xs, used) := calloc (S alk) qts  in
             ((mkQVar alk qty , xs), used)
         end.

End Internals.
Require Import Verse.
Require Import Verse.Error.

(* end hide *)

Require Import Verse.
Import Scope.

Ltac Function name func
  := ( let level0 := constr:(Scope.Cookup.specialise func) in
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
                                   pA lA func)
                   (** TODO: This can be a normal function application if
                             inferNesting carries around correctness proofs
                    *)

              ) (*(recover (Compile.targetTypes pvs))
                (recover (Compile.targetTypes lvs))*)
                eq_refl eq_refl)
     ).


Ltac Iterator name memty ifunc
  := ( let memtyTgt
           := constr:(recover (TypeSystem.Types.compile Compile.Config.typeCompiler memty)) in
       let level0       := constr:(Cookup.specialise ifunc) in
       let level0break  := (eval hnf in (inferNesting level0)) in
       let pvs          := constr:(fst level0break) in
       let level1       := constr:(snd level0break) in
       let lvs := (eval hnf in (fst (inferNesting level1))) in
       let pvt := constr:(recover (Compile.targetTypes pvs)) in
       let lvt := constr:(recover (Compile.targetTypes lvs)) in
       exact ((fun pfpvt pflvt =>
                 let (pA,n0) := Internals.calloc 0 pvt in
                 let (lA,n1) := Internals.calloc n0 lvt in
                 let streamVar := Internals.mkVar n1 (Compile.Config.streamOf memtyTgt) in
                 Compile.iterativeFunction name memty
                                           pvs lvs
                                           memtyTgt eq_refl
                                           streamVar
                                           pvt     lvt
                                           pfpvt   pflvt
                                           pA      lA
             ) eq_refl eq_refl ifunc
     )).

Require Export Verse.Target.C.Ast.
Require Export Verse.Target.C.Pretty.
