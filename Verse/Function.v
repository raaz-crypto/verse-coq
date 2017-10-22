Require Import Arch.
Require Import Error.
Require Import PrettyPrint.
Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Function.

  Variable var : varT.
  
  Record Function   := function
                         {
                           setup   : block var;
                           loop    : block var;
                           cleanup : block var;
                         }.

  Record FunVars   := funvars
                        {
                          fname   : string;
                          param   : list type;
                          local   : list type;
                        }.

  Inductive userTy : varT :=
  | inR ty : var ty -> userTy ty
  | onS ty : userTy ty
  .

  Definition userAlloc (local : list type) := allocation userTy local.

End Function.

Arguments inR [var ty] _.
Arguments onS [var] _.

Definition fscoped v p l := scoped v p (scoped v l (Function v)).

Definition func (reg : varT) (fv : FunVars) : Type := (forall (v : varT), fscoped v (param fv) (local fv)) * userAlloc reg (local fv).


Module FUNWRITE (A : ARCH) (F : FRAME A) (C : CODEGEN A).

  Inductive FunError : Prop :=
  | InstructionNotSupported : instruction A.machineVar -> FunError
  | NoLoopVariable          : FunError
  | TypeNotSupported        : type -> FunError
  | RegisterInUse (ty : type) : A.register ty -> FunError.

  Definition localAlloc (f : F.frameState) (ty : type) (ua : userTy A.register ty) : A.machineVar ty * F.frameState + { FunError } :=
    match ua with
    | inR r => match F.useRegister f r with
                   | {- x -} => {- x -}
                  | error e => error (match e with
                                           | or_introl _ _ => TypeNotSupported ty
                                           | or_intror _ _ => RegisterInUse r
                                           end)
                    end
    | onS ty  => match F.onStack f ty with
                   | {- x -} => {- x -}
                   | error _ => error (TypeNotSupported ty)
                   end
    end.
  
  Fixpoint pAlloc (p : list type) : forall (fr : F.frameState), F.frameState * allocation A.machineVar p + { FunError } :=
    fun (fr : F.frameState) => 
        match p with
        | [] => {- (fr, emptyAllocation A.machineVar) -}
        | ty :: pt => match F.paramAlloc fr ty with
                      | {- (vty, fr') -} => x <- pAlloc pt fr';
                                              let (fr'', a) := x in
                                              {- (fr'', (vty, a)) -}
                      | error _          => error (TypeNotSupported ty)
                      end
        end.

  Fixpoint lAlloc (l : list type) : forall (la : userAlloc A.register l) (fr : F.frameState), F.frameState * allocation A.machineVar l + { FunError } :=
    match l with
    | []       => fun _ (fr : F.frameState) =>
                    {- (fr, emptyAllocation A.machineVar) -}
    | ty :: lt => fun (la : userAlloc A.register (ty ::lt)) (fr : F.frameState) =>
                    x <- localAlloc fr (fst la);
                      let (vty, fr') := x in
                      y <- lAlloc lt (snd la) fr';
                        let (fr'', a) := y in
                        {- (fr'', (vty, a)) -}
    end.

  Arguments lAlloc [l] _ _.

  Definition fFill (fv : FunVars) (f : func A.register fv) : allocation A.machineVar (param fv) * F.frameState * Function A.machineVar + { FunError } :=
    let ef := F.emptyFrame (fname fv) in
    x <- pAlloc (param fv) ef;
      let (fr, pa) := x in
      y <- lAlloc (snd f) fr;
        let (fr', la) := y in
        {- (pa, fr', fill la (fill pa (fst f A.machineVar))) -}.

  Fixpoint blockWrite (b : block A.machineVar) : Doc + { FunError } :=
    let fix mapEmit (b : block A.machineVar) :=
    match b with
    | []      => {- [] -}
    | i :: bt => match C.emit i with
                 | {- d -} => x <- mapEmit bt;
                                {- d :: x -}
                 | error _ => error (InstructionNotSupported i)
                 end
    end in sepBy line <$> (mapEmit b).

  Definition gen (fv : FunVars) (f : func A.register fv) : Doc + { FunError } :=
      let fv' := {| fname := fname fv; param := A.Word :: param fv; local := local fv |} in
      let f'  : func A.register fv' :=
          ((fun v => @merge_scope _ [A.Word] _ _ (fun (n : v A.Word) => fst f v)), snd f) in
      match fFill f' with
      | {- (pa, fr, fn) -} => let fd := F.description fr in
                               match param fv as p return forall (x : allocation A.machineVar (A.Word :: p)), _ with
                               | [] => fun _ => error NoLoopVariable
                               | ty :: pt => 
                                 fun x => match x with
                                          | (count, (lv, pa')) =>
                                            C.prologue fd <>* nest 4 <$> (line <>* blockWrite (setup fn)
                                                                               *<> line *<>*
                                                                               (C.loopWrapper lv count <$> blockWrite (loop fn))
                                                                               *<> line *<>* blockWrite (cleanup fn)) *<> line *<> C.epilogue fd
                                          end 
                               end pa
      | error e => error e
      end
  .

  
End FUNWRITE.