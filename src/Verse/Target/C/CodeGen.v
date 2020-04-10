Require Import Verse.Language.Types.
Require Import Verse.Monoid.Semantics.
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

Module Internals.

  Import Verse.Target.C.Ast.Expr.

  (*
     CVars are the real variables however for streams we need a tuple
     of vars. We define the vars type for this

   *)

  Definition vars k (ty : C.Ast.type k)
    := match k with
       | direct => cvar ty
       | _      => match ty with
                  | ptrToArray n ty0 => (cvar ty * cvar uint64_t)%type
                  | _                => cvar ty
                  end
     end.

  (** Convert an expression to its corresponding variable *)
  Definition toVar {k} (t : type k)(e : Expr.expr)
    := match t as t0 return vars _ t0 with
       | ptrToArray _ _ => (e,e)
       | _              => e
       end.
  (** dereference a stream variables variable *)

  Definition deref {ty : type memory}
    : vars memory ty -> Expr.expr
    := match ty with
       | ptrToArray b t =>
         fun x : vars _ (ptrToArray _ _) => let (bptr, _) := x in (ptrDeref bptr)
       | array b t  => fun x : vars _ (array _ _) => ptrDeref x
       end.


  (** Get the stream pointer variable out of it *)
  Definition streamPtr {ty : type memory}
    : vars memory ty -> Expr.expr
    :=  match ty with
       | ptrToArray b t =>
         fun x : vars _ (ptrToArray _ _) => let (bptr, _) := x in bptr
       | array b t  => fun x : vars _ (array _ _) => x
       end.

  Definition counterVar {ty0 : type memory}{ty1 : type direct}
    : vars memory ty0 -> vars direct ty1
    := match ty0 with
       | ptrToArray _ _ =>
         fun x : vars _ (ptrToArray _ _) => let (_ , cVar) := x in toVar ty1 cVar
       | array b t  => fun x : vars _ (array _ _) => toVar ty1 x
       end.


  Fixpoint decl {k}{ty} : vars k ty ->  list declaration
   := match ty with
   | ptrToArray n t =>
       fun u : (expr * expr) %type =>
       let (bptr, ctr) := u in [ @declare k ty bptr; @declare direct uint64_t ctr]%list
   | _ => fun (u : expr) => [ @declare k ty u]%list
   end.

  Fixpoint trExpr {ty} (e : Ast.expr vars ty) : expr :=
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

  Definition trAssign {ty} (le : Ast.lexpr vars ty) (ex : Ast.expr vars ty) :=
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
  Definition trInst ty (inst : Ast.instruction vars ty) : statement + {TranslationError}
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

  Definition trStatement (s : Ast.statement vars) :=
    let single x := cons x nil in
    match s with
    | existT _ ty inst => single <$> trInst ty inst
    end.

End Internals.

Module Config <: CONFIG.

  Definition statement   := C.Ast.statement.
  Definition programLine := Ast.line.

  Instance target_semantics : semantics (list C.Ast.statement + {TranslationError})
    := {| types :=  c_type_system;
          variables := Internals.vars;
          denote   := Internals.trStatement
       |}.

  Definition typeCompiler : TypeSystem.compiler verse_type_system c_type_system
    :=
      let targetTs := TypeSystem.result types in
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


  Definition ptrOf {k} (block : typeOf c_type_system k)

    := match block in type k0
             return  match k0 with
                     | direct => IDProp
                     | memory => type memory
                     end with
       | array b ty0  | ptrToArray b ty0 => ptrToArray b ty0
       | _            => idProp
       end.
(*
  Definition deref  {k} {block : typeOf c_type_system k}
             (v : variables k block)
    := match block as block0 in type k0
             return  match k0 with
                     | direct => IDProp
                     | memory => variables memory (@ptrOf memory block0)
                     end with
       | array b ty0  | ptrToArray b ty0 => ptrToArray b ty0
       | _            => idProp
       end.
 *)
  Definition streamOf (block : typeOf c_type_system memory)
    : typeOf c_type_system memory
    := ptrOf block.

  (*
  Definition deref {k} (ty : type k)
             variables k ty).
    := match ty with
   *)
  Definition dereference {block : type memory}
    : variables memory (streamOf block) -> variables memory block
    := fun x => Internals.toVar block (Internals.deref x ).

  Definition mapOverBlocks {block}
             (streamVar : variables memory (streamOf block))
             (body : list statement)
             : list statement
    := let blockVar := Internals.streamPtr streamVar in
       let counter : variables direct uint64_t := Internals.counterVar streamVar  in
       [ whileLoop (Expr.gt_zero counter)
                   (Braces
                      (body ++ [ increment blockVar ; decrement counter ]
                   ))
       ]%list.


  Fixpoint allocToList {n} (st : Scope.type types n)
    :  Scope.allocation variables st -> list declaration :=
    match st as st0 return Scope.allocation variables st0 -> list declaration
    with
    | []       => fun _ => []%list
    | (existT _ k ty :: xs) =>
      fun arg => let (u, ap) := arg in
              let ds := Internals.decl u in
              (ds ++ allocToList xs ap)%list
    end.

  Arguments allocToList [n st].

  Definition makeFunction (name : Set) (fname : name)(fsig : funSig types variables)
             (body : list statement)
    := let ps := params (allocToList (Target.parameters fsig)) in
       let ls := List.map declareStmt (allocToList (Target.locals fsig)) in
       let rs := List.map declareStmt (allocToList (Target.registers fsig)) in
       function fname ps (Braces (ls ++ rs ++ body))%list.

End Config.
