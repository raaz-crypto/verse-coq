Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Require Import Verse.Target.
Require Import Verse.Target.C.Ast.
Require Import Verse.Error.
Require Import Verse.Nibble.
Require        Verse.Scope.
Require Import List.
Import ListNotations.
Require Vector.
Import Vector.VectorNotations.

Module Config <: CONFIG.

  Definition statement   := C.Ast.statement.
  Definition programLine := Ast.line.

  Definition typeS     := c_type_system.

  Definition variables := cvar.

  Definition typeCompiler : TypeSystem.compiler verse_type_system c_type_system
    :=
      let targetTs := TypeSystem.result typeS in
      let trType (ty : Types.type direct) : typeOf targetTs direct
           := let couldNotError := error (CouldNotTranslate ty)
              in match ty with
                 | Word8  => {- uint8_t  -}
                 | Word16 => {- uint16_t -}
                 | Word32 => {- uint32_t -}
                 | Word64 => {- uint64_t -}
                 | _ => couldNotError
                 end in
      let trConst (ty : Types.type direct)
          : Types.const ty -> constOf targetTs (trType ty)
          := match ty with
             | word n =>
               match n as n0
                     return Types.const (word n0)
                            -> constOf targetTs (trType (word n0))
               with
               | 0 | 1 | 2 | 3  => fun x => Vector.to_list x
               | _ => fun x : _ => error (CouldNotTranslate x)
               end
             | multiword _ _  => fun x => error (CouldNotTranslate x)
             end in
      verseTranslation trType trConst.

  Definition pointerType (memty : Types.type memory) good
             (_ : Types.compile typeCompiler memty = {- good -})
    : typeOf c_type_system memory
    := match good with
       | array b ty0 => ptrToArray b ty0
       | _           => good
       end.

  Definition dereference : forall memty good (pf : Types.compile typeCompiler memty = {- good -}),
      variables memory (pointerType memty good pf) -> variables memory good :=
   fun _ _ _ x => Expr.ptrDeref x.

  Import Verse.Target.C.Ast.Expr.

  Fixpoint trExpr {ty} (e : Ast.expr cvar ty) : expr :=
    match e with
    | Ast.cval   c     => verse_const _ c
    | Ast.valueOf le   => match le with
                         | Ast.var v => v
                         | @Ast.deref _ _ _ b endn arr (exist _ i _) =>
                           let arrI := match b with
                                       | 1 => ptrDeref arr (* array[1] = pointer *)
                                       | _ => index arr i
                                       end in
                           match endn with
                           | hostE => arrI
                           | _     => convert_from endn ty arrI
                           end
                         end
    | @Ast.app _ _ _  _ o v
      => let args := Vector.map trExpr v in
        match o with
        | Ast.cop co => app co
        | Ast.rotL n => fun cve => rotateL ty (Vector.hd cve, n)
        | Ast.rotR n => fun cve => rotateR ty (Vector.hd cve, n)
        end args
    end.

  Definition trAssign {ty} (le : Ast.lexpr cvar ty) (ex : Ast.expr cvar ty) :=
    let endianConversion endn cex :=
        match endn, cex with
        | hostE, _                            => cex
        | _, _                                => convert_to endn ty cex
        end in

    match le with
    | Ast.var v => assign v (trExpr ex)
    | @Ast.deref _ _ _ _ endn arr (exist _ i _)
      => assign (index arr i) (endianConversion endn (trExpr ex))
    end.

  (** This definition is giving some warning in terms of implicits please check *)
  Definition trInst ty (inst : Ast.instruction cvar ty) : statement + {TranslationError}
    := let getCOP n (o : Ast.op n)
           := match o with
              | Ast.cop co => {- co -}
              | _          => error (CouldNotTranslateBecause inst UpdatesNotForRotatesInC)
              end in
       let handleUpdate le (func : expr -> statement) :=
           match le with
           | Ast.var v => {- func v -}
           | @Ast.deref _ _ _ _ endn arr (exist _ i _)
             => match endn with
               | hostE => {- func (index arr i) -}
               | _     => error (CouldNotTranslateBecause inst UpdatesNeedHostEndian)
               end
           end
       in
       match inst with
       | Ast.assign le ex     => {- trAssign le ex -}
       | @Ast.update _ _ _ le n o vex  => co <- getCOP (S n) o;
                                  handleUpdate le (fun lhs => update lhs co (Vector.map trExpr vex))
       | Ast.increment le     => handleUpdate le increment
       | Ast.decrement le     => handleUpdate le decrement
       | Ast.moveTo le v      => {- trAssign le (Ast.valueOf (Ast.var v)) -}
       | _                    => error (CouldNotTranslateBecause inst ExplicitClobberNotInC)
      end.

  Definition trStatement (s : Ast.statement cvar) :=
    match s with
    | existT _ ty inst => trInst ty inst
    end.


  Definition compileCode : Language.Ast.code variables -> list statement + {TranslationError}
    := fun cs => pullOutList (List.map trStatement cs).

  Definition mapOverBlocks mem ty
             (blockPtrVar : variables memory mem)
             (ctrVar : variables direct ty)
             (body : list statement)
             : list statement
    := [ whileLoop (gt_zero ctrVar)
                   (Braces
                      (body ++ [ increment blockPtrVar ; decrement ctrVar ]
                   ))
       ]%list.


  Fixpoint allocToList {n} (st : Scope.type typeS n)
    :  Scope.allocation variables st -> list declaration :=
    match st as st0 return Scope.allocation variables st0 -> list declaration
    with
    | []       => fun _ => []%list
    | (existT _ k ty :: xs) =>
      fun arg => let (u, ap) := arg in
              (@declare k ty u :: allocToList xs ap)%list
    end.

  Arguments allocToList [n st].

  Definition makeFunction (name : Set) (fname : name)(fsig : funSig typeS variables)
             (body : list statement)
    := let ps := params (allocToList (Target.parameters fsig)) in
       let ls := List.map declareStmt (allocToList (Target.locals fsig)) in
       let rs := List.map declareStmt (allocToList (Target.registers fsig)) in
       function fname ps (Braces (ls ++ rs ++ body))%list.

End Config.
