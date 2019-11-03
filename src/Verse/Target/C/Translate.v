Require Import Verse.Language.Types.
Require Import Verse.Target.C.Ast.
Require Import Verse.Error.
Require Import Verse.Nibble.

Module Internal.

  Definition tgt  := resultSystem c_type_system.

  Definition trType (ty : Types.type direct) : typeOf tgt direct
    := let couldNotError := error (CouldNotTranslate ty)
       in match ty with
          | Word8  => {- uint8_t  -}
          | Word16 => {- uint16_t -}
          | Word32 => {- uint32_t -}
          | Word64 => {- uint64_t -}
          | _ => couldNotError
          end.

  Definition trConst (ty : Types.type direct)
    : Types.const ty -> constOf tgt (trType ty)
    := match ty with
       | word n =>
         match n as n0
               return Types.const (word n0)
                      -> constOf tgt (trType (word n0))
         with
         | 0 | 1 | 2 | 3  => @toNibbleTuple _
         | _ => fun x : _ => error (CouldNotTranslate x)
         end
       | multiword _ _  => fun x => error (CouldNotTranslate x)
       end.

End Internal.

Canonical Structure c_type_compile : typeCompile verse_type_system c_type_system
  := verseTranslation Internal.trType Internal.trConst.



Require Verse.Language.Ast.
Import Verse.Target.C.Ast.Expr.
Require Vector.
Import Vector.VectorNotations.

Module CompilerInternals.

  Fixpoint trExpr {ty} (e : Ast.expr cvar ty) : expr :=
    match e with
    | Ast.cval   c     => verse_const _ c
    | Ast.valueOf le   => match le with
                         | Ast.var v => v
                         | @Ast.deref _ _ _ _ endn arr (exist _ i _) =>
                           let arrI := index arr i in
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
        | littleE, convert_from littleE _ cep => cep
        | bigE, convert_from bigE _ cep       => cep
        | _, _                                => convert_to endn ty cex
        end in

    match le with
    | Ast.var v => assign v (trExpr ex)
    | @Ast.deref _ _ _ _ endn arr (exist _ i _)
      => assign (index arr i) (endianConversion endn (trExpr ex))
    end.

  (** This definition is giving some warning in terms of implicits please check *)
  Definition trInst ty (inst : Ast.instruction cvar ty) : statement + {TranslationError}
    := let getCOP {n}(o : Ast.op n)
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
       | Ast.update le o vex  => co <- getCOP o;
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

  Definition trCode cs := merge _ _ (List.map trStatement cs).

End CompilerInternals.
