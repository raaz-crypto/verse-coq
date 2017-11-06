Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Language.
Require Import Verse.Syntax.
Require Import Verse.Arch.
Require Import Verse.Compile.
Require Import Verse.Error.
Require Import Verse.PrettyPrint.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section SeqFunction.

  Variable blockType : type.
  
  Record ScopedSeqFunc var := scopedseqfunc {
                                prologue : block var;
                                loop     : var (Ref blockType) -> block var;
                                epilogue : block var
                              }.

End SeqFunction.


Module SeqCompiler (A : ARCH) (F : FRAME A) (C : CODEGEN A).

  Module ACompiler := Compiler A F C.
  Import ACompiler.

  Record SeqFunction blockType var := seqfunction {
                                          msg    : var (Ref blockType);
                                          count  : var (A.Word);
                                          pre    : block var;
                                          lblock : block var;
                                          epi    : block var
                                        }.

  Section PreProcess.
    Variable var : varT.
    Variable count : nat.
    Variable blockType : type.

    Variable pts lts : list type.

    Variable rts : list type.

    (** Its register variables *)
    Variable regs : allocation A.register rts.

    Definition preProcess (sf : forall v, BodyType (ScopedSeqFunc blockType) pts lts rts v) :=
      fun v : varT =>
        fun lv : v (Ref blockType) => 
          fun n : v A.Word =>
            let a (x : ScopedSeqFunc blockType v) :=
                seqfunction blockType
                            lv
                            n
                            (prologue x)
                            (loop x lv)
                            (epilogue x)
            in
            scopedAppConst _ (scopedAppConst _ (scopedAppConst _ a)) (sf v).

  End PreProcess.

  Definition compileSeqFunc b (f : SeqFunction b A.machineVar) :=
    compileInstructions (pre f) *<>*
    C.loopWrapper (msg f) (count f) <$>
                        compileInstructions (lblock f) *<>*
    compileInstructions (epi f).

  Arguments preProcess [blockType pts lts rts] _ _ _ _.

  Definition compile name b pts lts rts regs f
    :=
      result <-  @genCompile (SeqFunction b) name (Ref b :: A.Word :: pts) lts rts regs (preProcess f);
        let (descr, code) := result  in
        delimit (C.prologue descr)  (C.epilogue descr) <$> (compileSeqFunc code).

End SeqCompiler.
