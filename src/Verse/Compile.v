Require Import Arch.
Require Import Error.
Require Import PrettyPrint.
Require Import Types.Internal.
Require Import Syntax.
Require Import Language.
Require Import String.
Require Import Coq.Sets.Ensembles.

Require Import Vector.
Import VectorNotations.

Set Implicit Arguments.

(** * Compilation.

This module exposes code to compile verse programs to machine code.

 *)

(**

Compilation is parameterised by the architecture, the frame
management associated with the architecture and the code generator.

 *)
Module Compiler (A : ARCH) (F : FRAME A) (C : CODEGEN A).

  (** We begin by defining the errors that can arise when code fragments are
      compiled.
   *)

  Inductive AllocationError : Prop :=
  | UnavailableRegister    : forall {k}{ty : A.mType k}, A.register ty -> AllocationError
  | UnsupportedLocalArray  : type memory -> AllocationError.

  Inductive CompileError : Prop :=
  | instructionError       : UnsupportedInstruction -> CompileError
  | typeError              : UnsupportedType -> CompileError
  | allocationError        : AllocationError -> CompileError.

  Instance liftTypeError : Castable UnsupportedType CompileError :=
    { cast := typeError }.

  Instance liftInstructionError : Castable (UnsupportedInstruction) CompileError :=
    { cast := instructionError }.

  Instance liftAllocationError : Castable AllocationError CompileError :=
    { cast := allocationError }.

  Let checkTy k (ty : type k) := match isErr (typeDenote ty) with
                                 | left p => {- p -}
                                 | right _ => error (unsupported ty)
                                 end.

  (** Lifting a function on supported types to a function on all types that throws errors *)
  Local Definition checkApp k (ty : type k) T f
    : T + {CompileError} :=
    match isErr (typeDenote ty) with
    | left p  => f p
    | right p => liftErr (error (unsupported ty))
    end.

  Section CodeDenote.

    Variable v : VariableT.
    Variable vTrans : forall k (ty : type k) (p : noErr (typeDenote ty)),
                             v ty -> A.mVar (getT p).

    Definition argDenote aK k (ty : type k) (p : noErr (typeDenote ty)) (a : (arg v aK ty))
      : C.mArg A.mVar (getT p) + {CompileError}.
      simple refine
             (match a in arg _ _ ty' with
              | var x                     => fun p' =>
                                               {- mkVar A.mVar _ (vTrans p' x) -}
              | Ast.const c               => fun p' =>
                                               {- mkConst A.mVar (A.mConstantDenote _ p' c) -}
              | @Ast.index _ _ b e ty x i => fun p' =>
                                               checkApp (array b e ty)
                                                        (fun p'' => {- mkIndex A.mVar b e
                                                                               (getT p') _ _
                                                                               (proj1_sig i) -})
              end p);
        rewrite <- (getTgetsT p').
      exact p''.
      exact (@vTrans _ (array b e ty) p'' x).
    Defined.
    (* argDenote cannot be written without it's argument p as the return
      type is unspecifiable otherwise
     *)

    Definition instDenote (i : instruction v) : C.mInstruction + {CompileError}.
      simple refine
             match i with
             | increment la => checkApp _ (fun p => collectErr (mkIncrement <$> (argDenote p la)))
             | decrement la => checkApp _ (fun p => collectErr (mkIncrement <$> (argDenote p la)))
             | assign a => match a with
                           | update1 o la           => checkApp _ (fun p => collectErr (mkUpdate1 o <$> argDenote p la))
                           | update2 o la ra        => checkApp _ (fun p => collectErr (mkUpdate2 o <$> argDenote p la
                                                                                                  <*> argDenote p ra))
                           | assign2 o la ra        => checkApp _ (fun p => collectErr (mkAssign2 o <$> argDenote p la
                                                                                                  <*> argDenote p ra))
                           | assign3 o la1 la2
                                     ra             => checkApp _ (fun p => collectErr (mkAssign3 o <$> argDenote p la1
                                                                                                  <*> argDenote p la2
                                                                                                  <*> argDenote p ra))
                           | extassign3 o la1 la2
                                        ra1 ra2     => checkApp _ (fun p => collectErr (mkExtassign3 o <$> argDenote p la1
                                                                                                     <*> argDenote p la2
                                                                                                     <*> argDenote p ra1
                                                                                                     <*> argDenote p ra2))
                           | extassign4 o la1 la2
                                        ra1 ra2 ra3 => checkApp _ (fun p => collectErr (mkExtassign4 o <$> argDenote p la1
                                                                                                     <*> argDenote p la2
                                                                                                     <*> argDenote p ra1
                                                                                                     <*> argDenote p ra2
                                                                                                     <*> argDenote p ra3))
                           end
             | @moveTo _ b e ty x i lv => collectErr (checkApp ty (fun p => checkApp (array b e ty)
                                                                                     (fun p' => {- mkMoveTo b e _ _ (proj1_sig i) (vTrans p lv) -})))
             | CLOBBER _  => {- mkNOP -}
             end
      ;
      rewrite <- (getTgetsT p).
      exact p'.
      exact (@vTrans _ (array b e ty) p' x).
    Defined.

    Definition compileInstructions insts :=
      let compile := fun i => liftErr (instDenote i) in
      merge (List.map compile insts).

  End CodeDenote.

  (* Internal module to hide local variables *)
  Module Internal.

    (** Type definition marking a list of types as supported *)
    Local Definition suppTypes {n} (l : Vector.t (some type) n) :=
      allocation (fun k (ty : type k) => noErr (typeDenote ty)) l.

    (** suppTypes works well with append *)
    Local Fixpoint stAppend n1 n2
                            (l1 : Vector.t (some type) n1)
                            (l2 : Vector.t (some type) n2)
      : suppTypes l1 -> suppTypes l2 ->  suppTypes (Vector.append l1 l2) :=
      (* why is notation not working here *)
      match l1 with
      | []                   => fun _ p2  => p2
      | _ :: lt => fun p1 p2 => (fst p1, stAppend lt l2 (snd p1) p2)
      end.

    Arguments stAppend [n1 n2 l1 l2] _ _.

    (** Generate a proof of a type list being supported or throw an error *)
    Local Fixpoint checkTypes {n} (l : Vector.t (some type) n)
      : suppTypes l + {UnsupportedType} :=
      match l with
      | []                  => {- tt -}
      | existT _ _ ty :: lt => match isErr (typeDenote ty) with
                               | left p  => pair p <$> checkTypes lt
                               | right p => error (unsupported ty)
                               end
      end.

    (** Denotation of a list of supported types *)
    Local Fixpoint typeListDenote {n}
      : forall (l : Vector.t (some type) n), suppTypes l -> Vector.t (some A.mType) n :=
      match n with
      | 0   => fun _ _    => []
      | S m => fun l' pl' => existT _ _ (getT (fst pl')) :: typeListDenote (tl l') (snd pl')
      end.

    (** Type list denotes work well with append *)
    Fixpoint tlDenoteAppends {n1 n2}
                             (l1 : Vector.t (some type) n1) (l2 : Vector.t (some type) n2)
                             (gl1 : suppTypes l1) (gl2 : suppTypes l2) {struct l1}
      : typeListDenote (append l1 l2) (stAppend gl1 gl2) =
        append (typeListDenote l1 gl1) (typeListDenote l2 gl2).
      induction l1; simpl.
      congruence.
      f_equal; apply tlDenoteAppends.
    Defined.

    Arguments tlDenoteAppends [n1 n2 l1 l2] _ _.

    (** A machine variable allocation corresponding to a list of supported types *)
    Local Definition Allocation (v : GenVariableT A.mType) n (l : Vector.t (some type) n)
                                (ml : suppTypes l)
      := allocation v (typeListDenote l ml).

    Arguments Allocation _ [n l] _.

    Local Definition mergeAlloc v n1 (l1 : Vector.t (some type) n1)
                                n2 (l2 : Vector.t (some type) n2)
                                (gl1 : suppTypes l1) (gl2 : suppTypes l2)
                                (a1 : Allocation v gl1) (a2 : Allocation v gl2)
      : Allocation v (stAppend gl1 gl2) :=
      let alloc := mergeAllocation a1 a2 in
      eq_rect_r _ alloc (tlDenoteAppends gl1 gl2).

    Arguments mergeAlloc [v n1 l1 n2 l2 gl1 gl2] _ _.

    Local Definition FAllocation n (l : Vector.t (some type) n) (ml : suppTypes l)
      := (Allocation A.mVar ml * F.frameState)%type.

    (** Generate a frame with the given set of parameters *)
    Fixpoint params {n} s0 (l : Vector.t (some type) n)
      : forall (p : suppTypes l), FAllocation l p :=
      match l with
      | []           => fun _ => (emptyAllocation A.mVar, s0)
      | (existT _ _ ty :: rest) => fun p => 
                                     let (v, s1)  := (F.addParam s0 (getT (fst p))) in
                                     let (vs, s2) := params s1 rest (snd p) in
                                     ((v,vs), s2)
      end.

    (** Generate a frame with the given set of stack varaibles or die trying *)
    Fixpoint stacks {n} s0 (l : Vector.t (some type) n)
      : forall (p : suppTypes l), FAllocation l p + {AllocationError} :=
      match l with
      | []                        => fun _ => {- (emptyAllocation A.mVar, s0) -}
      | (existT _ memory ty :: _) => fun _ => error (UnsupportedLocalArray ty)
      | (existT _ direct ty :: rest) => fun p => 
                                          let a1 := F.stackAlloc s0 (getT (fst p)) in
                                          let (v, s1) := a1
                                          in a2 <- stacks s1 rest (snd p);
                                               let (vs,s2) := a2
                                               in {- ((v,vs), s2) -}
      end.

    (** Generate a frame given an allocation of the local register variables *)
    Fixpoint registers {n} (l : Vector.t (some type) n)
      : forall p : suppTypes l, F.frameState ->
                                Allocation A.register p ->
                                FAllocation l p + {AllocationError}  :=
      match l with
      | []          => fun p s0 _  => {- (emptyAllocation A.mVar, s0) -}
      | (existT _ memory ty :: _) => fun _ _ _ => error (UnsupportedLocalArray ty)
      | (existT _ direct ty :: tys)
        => fun p s0 rs =>
             let (r,rest) := rs in
             match F.useRegister s0 r with
             | Some s1 => restAlloc <- registers tys (snd p) s1 rest;
                            let (a,finalState) := restAlloc
                            in {- ((A.embedRegister r, a), finalState) -}
             | None    => error (UnavailableRegister r)
             end
      end.

    Arguments params [n] _ [l] _.
    Arguments stacks [n] _ [l] _.
    Arguments registers [n] [l] _ _ _.

    (** Provide the translation from ScopeVar to the explicit machine
        allocation
     *)
    Fixpoint makeVTrans n (l : Vector.t (some type) n)
             (pl : suppTypes l) (a : Allocation A.mVar pl)
             k (ty : type k) (p : noErr (typeDenote ty)) (v : scopeVar l ty) :
      A.mVar (getT p).
      refine
        (match v in scopeVar l' ty' return forall (pl' : suppTypes l')
                                                  (a' : Allocation A.mVar pl')
                                                  (p' : noErr (typeDenote ty')),
                                                  A.mVar (getT p')
        with
        | headVar _ => _
        | @restVar m v0 k0 ty0 s => fun pl' a' p' =>
                                      makeVTrans m (tl v0) (snd pl') (snd a')
                                                 k0 ty0 p' s

         end pl a p).
      intros.
      rewrite (getTunique p' (fst pl')).
      exact (fst a').
    Defined.

    Arguments makeVTrans [n l pl] _ [k ty] _ _.

    Section Function.

      Variable startState : F.frameState.

      (** Its parameters and stack variables *)
      Variable nP nS nR : nat.

      Variable parameterTypes : Vector.t (some type) nP.
      Variable stackTypes : Vector.t (some type) nS.

      Variable registerTypes : Vector.t (some type) nR.

      (** Its register variables *)
      Variable registerVariables : forall (p : suppTypes registerTypes),
          Allocation A.register p.

      Local Definition BodyType BODY v := scoped v parameterTypes
                                            (scoped v stackTypes
                                                    (scoped v registerTypes (BODY v))
                                            ).

      (** Fill a generic Verse code block with the 'most general'
          VariableT corresponding to it's scope *)
      Definition fillVars BODY (functionBody  : forall v, BodyType BODY v) :=
        fillDummy (fun v => mergeScope (mergeScope (functionBody v))).

      (** Use the frame routines to provide an allocation into machine variables *)
      Definition mkAlloc (pp : suppTypes parameterTypes)
                 (sp : suppTypes stackTypes)
                 (rp : suppTypes registerTypes)
                 (regs : forall x, Allocation _ x)
        : _ + {AllocationError}
        := let pA := params startState pp in
           let (pVars, paramState) := pA in
           lA *<- stacks paramState sp;
             let (sVars, stackState) := lA in
             rA *<- registers rp stackState (regs rp);
               let (rVars, finalState) := rA in
               {- (finalState, mergeAlloc (mergeAlloc pVars sVars) rVars) -}.

    End Function.

    Arguments mkAlloc _ [nP nS nR parameterTypes stackTypes registerTypes] _ _ _ _.

    Section IteratorF.
      
      Variable startState : F.frameState.

      (** Its parameters and stack variables *)
      Variable nP nS nR : nat.

      Variable codeT : type memory.
      Variable parameterTypes : Vector.t (some type) nP.
      Variable stackTypes : Vector.t (some type) nS.

      Variable registerTypes : Vector.t (some type) nR.

      (** Its register variables *)
      Variable registerVariables : forall (p : suppTypes registerTypes),
          Allocation A.register p.

      Local Record iterBlocks v := itB { setup : code v;
                                         process : code v;
                                         finalise : code v
                                       }.

      Local Definition mkBlocks v x (i : iterator codeT v) :=
        {| setup    := Ast.setup i;
           process  := Ast.process i x;
           finalise := Ast.finalise i
        |}.

      (** Add the loop variable to the scope *)
      Local Definition scopeLoopVar iterF v
        : BodyType ((existT _ _ codeT) :: parameterTypes)
                   stackTypes registerTypes
                   iterBlocks v :=
        fun codeV => appScoped (appScoped (appScoped (mkBlocks codeV))) (iterF v).

      (** Generate allocations for an iterator function *)
      Local Definition mkIAlloc (pT : noErr (typeDenote codeT))
            (codeV : A.mVar (getT pT))
            (pp : suppTypes parameterTypes)
            (sp : suppTypes stackTypes) (rp : suppTypes registerTypes)
            (regs : forall x, Allocation _ x)
        : _ + {AllocationError}
        := let pA := params startState pp in
           let (pVars, paramState) := pA in
           let pts' := existT _ _ codeT :: parameterTypes in
           let pp' : suppTypes pts' := (pT, pp) in
           let pVars' : Allocation A.mVar pp' := (codeV, pVars) in
           lA *<- stacks paramState sp;
             let (sVars, stackState) := lA in
             rA *<- registers rp stackState (regs rp);
               let (rVars, finalState) := rA in
               {- (finalState, mergeAlloc (mergeAlloc pVars' sVars) rVars) -}.

    End IteratorF.
    
    Arguments scopeLoopVar [nP nS nR] _ [parameterTypes stackTypes registerTypes] _.
    Arguments mkIAlloc _ [nP nS nR codeT parameterTypes stackTypes registerTypes] _ _ _ _ _ _.

    (** Compile generic Verse code into machine instructions *)
    Definition compile {nP nL nR} name
                       (pts : Vector.t (some type) nP)
                       (lts : Vector.t (some type) nL)
                       (rts : Vector.t (some type) nR) regs f
      := let vCode := fillVars pts lts rts code f in
         let state := F.emptyFrame name in
         pp *<- checkTypes pts;
           sp *<- checkTypes lts;
           rp *<- checkTypes rts;
           cc *<- mkAlloc state pp sp rp regs;
           let (finalState, alloc) := cc in
           let vTrans := makeVTrans alloc in
           pair (F.description finalState) <$> compileInstructions vTrans vCode. 

    Definition compileIterator {nP nL nR} ty name (pts : Vector.t (some type) nP)
               (lts : Vector.t (some type) nL)
               (rts : Vector.t (some type) nR) regs iterF
      := let pts' := existT _ _ ty :: pts in
         let iterB := scopeLoopVar ty iterF in
         let vCode := fillVars pts' lts rts iterBlocks iterB in
         pT *<- checkTy ty;
           let S := F.iterateFrame name (getT pT) in
           let (iterVars, state) := S in
           let (iterpar, loopvar)  := iterVars in
           let (codeVT, countV) := iterpar in
           let 'existT _ _ codeV := codeVT in
           pp *<- checkTypes pts;
             sp *<- checkTypes lts;
             rp *<- checkTypes rts;
             cc *<- mkIAlloc state pT loopvar pp sp rp regs;
             let (finalState, alloc) := cc in
             let vTrans := makeVTrans alloc in
             mSetup <- compileInstructions vTrans (setup vCode);
               mProcess <- compileInstructions vTrans (process vCode);
               mFinalise <- compileInstructions vTrans (finalise vCode);
               let mLoop := C.loopWrapper codeV countV mProcess in
               let mCode := List.app (List.app mSetup mLoop) mFinalise in
               {- pair (F.description finalState) mCode -}.

    (** Pretty printing *)

    Let write insts := C.emit insts.

    Let wrap descr code := C.makeFunction descr code.

    Definition show mCode : Doc + {CompileError} :=
      (fun code : A.functionDescription * list C.mInstruction =>
         let (descr, code) := code in wrap descr (write code))
        <$> mCode.

    Arguments compile [nP nL nR] _ _ _ [rts] _ _.
    Arguments compileIterator [nP nL nR] _ _ _ _ [rts] _ _.

  End Internal.

End Compiler.
