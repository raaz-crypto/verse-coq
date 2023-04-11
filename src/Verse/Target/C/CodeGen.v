(* begin hide *)
Require Import Verse.Language.Types.
Require Import Verse.Monoid.Semantics.
Require Import Verse.Monoid.Interface.
Require Import Verse.TypeSystem.
Require Import Verse.Target.
Require Import Verse.Target.C.Ast.
(* TODO : Importing Verse.Ast above C.Ast causes a name conflict *)
Require Import Verse.Ast.
Require Import Verse.Error.
Require Import Verse.Nibble.
Require        Verse.Scope.

Require Vector.
Import Vector.VectorNotations.
Require Import List.
Import ListNotations.
(* end hide *)

(** * Target configuration for Portable C.

This module exposes a target configuration module for the C language
for use in generating portable C code. We start with definition some
helper functions and types and wrap it inside an Internal module so
that it is not available outside.

*)

Module Internals.

  Import Verse.Target.C.Ast.Expr.

  (** ** Target variables are not [cvar].

    We finally want the code to be pretty printed and hence the
    variable used in the final C code should be of type
    [cvar]. However, a stream in C is represented by a pointer and a
    counter and hence require two [cvars]. Thus we will be using the
    following variable in the target configuration for C.

    The inner match is sufficient to make coq's type checker happy but
    the advantage of this outer match is that it clearly says that the
    variable for a [direct] type is just a [cvar].  This makes writing
    the instruction translations easier.

   *)

  Definition targetTs := TypeSystem.result c_type_system.

  Definition trType (ty : Types.type direct) : typeOf targetTs direct
    := let couldNotError := error (CouldNotTranslate ty)
       in match ty with
          | Word8  => {- uint8_t  -}
          | Word16 => {- uint16_t -}
          | Word32 => {- uint32_t -}
          | Word64 => {- uint64_t -}
          | _ => couldNotError
          end.

  Definition trConst [ty : Types.type direct]
    : Types.const ty -> constOf targetTs (trType ty)
    := match ty with
       | word n =>
           match n as n0
                 return Types.const (word n0)
                        -> constOf targetTs (trType (word n0))
           with
           | 0 | 1 | 2 | 3  => fun x => Vector.to_list (Nibble.fromBv x)
           | _ => fun x : _ => error (CouldNotTranslate x)
           end
       | multiword _ _  => fun x => error (CouldNotTranslate x)
       end.

  Definition trOp (ty : Types.type direct) n
    : operator verse_type_system ty n ->
      operator targetTs (trType ty) n
    := fun op : Types.op n =>
         match trType ty as x return (operator targetTs x n) with
         | error e => error e
         | _ => op
         end.

  Definition variables : Variables.U c_type_system
    := fun (ty : some type) =>
         match projT1 ty with
         | direct => expr
         | _      => match projT2 ty with
                    | ptrToArray n ty0 => (expr * expr)%type
                    | _                => expr
                    end
         end.
  Definition blockPtr : expr * expr -> expr := fst.
  Definition counter  : expr * expr -> expr := snd.

  (** Generates a list of declarations variables. For stream types it
     generates declaration for the associated pointer and the counter
     variables *)

  Definition decl {k ty} : variables (existT _ k ty) -> list declaration
    := match ty as ty0 in type k0
             return variables (existT _ k0 ty0) -> list declaration
       with
       | ptrToArray _ _
         => fun u => [ declare (ty:=ty)       (blockPtr u);
                   declare (ty:=uint64_t) (counter u)
             ]
       | _ => fun u =>  [ declare (ty:=ty) u]
       end%list.

  Definition init n
    := initialize_variable uint64_t
                           repCtr
                           (verse_const uint64_t
                                        (trConst (natToConst Word64 n))).

  (* begin hide *)
  Fixpoint trExpr {ty} (e : Ast.expr variables ty) : expr :=
    match e with
    | @Ast.cval _ _ ty0 c     => verse_const ty0 c
    | Ast.valueOf le   => match le with
                         | Ast.var v => v
                         | @Ast.deref _ _ ty0 b endn arr (exist _ i _) =>
                           let arrI := match b with
                                       | 1 => ptrDeref arr (* array[1] = pointer *)
                                       | _ => index arr i
                                       end in
                           match endn with
                           | hostE => arrI
                           | _     => convert_from endn ty0 arrI
                           end
                         end
    | Ast.binOp o e0 e1 => app o [trExpr e0; trExpr e1]%vector
    | @Ast.uniOp _ _ ty0 o e0 =>
      match o with
      | rotL n => rotateL ty0 (trExpr e0 , n)
      | rotR n => rotateR ty0 (trExpr e0, n)
      | x      => app x [trExpr e0]%vector
      end
    end.

  Definition trAssign {ty} (le : Ast.lexpr variables ty) (ex : Ast.expr variables ty) :=
    match le with
    | Ast.var v => C.Ast.assign v (trExpr ex)
    | @Ast.deref _ _ ty0 _ endn arr (exist _ i _)
      => let endianConversion endn cex :=
          match endn, cex with
          | hostE, _                            => cex
          | _, _                                => convert_to endn ty0 cex
          end in
        C.Ast.assign (index arr i) (endianConversion endn (trExpr ex))
    end.

  (* TODO : This definition is giving some warning in terms of implicits please check *)
  Definition trInst ty (inst : Ast.instruction variables ty) : C.Ast.statement + {TranslationError}
    := let getCOP n (o : Ast.op n)
           := match o with
              | rotL _ | rotR _ => error (CouldNotTranslateBecause inst UpdatesNotForRotatesInC)
              | o => {- o -}
              end in
       let handleUpdate [ty] (le : lexpr variables ty) (func : expr -> C.Ast.statement) :=
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
       | assign le ex     => {- trAssign le ex -}
       | binopUpdate le o vex
         => do co <- getCOP 2 o ;;
              handleUpdate le (fun lhs => C.Ast.update lhs co (Vector.map trExpr [vex]%vector))
       | uniopUpdate le o
         => do co <- getCOP 1 o ;;
              handleUpdate le (fun lhs => C.Ast.update lhs co []%vector)
       (* TODO : The next is an ugly hack. Works mostly because the
       last match clause exists. *)
       | @Ast.moveTo _ _ (existT _ direct _) le v      => {- trAssign le (Ast.valueOf (Ast.var v)) -}
       | _                    => error (CouldNotTranslateBecause inst ExplicitClobberNotInC)
      end.


  (* end hide *)
  Definition trStatement (s : statement variables) :=
    let single x := cons x nil in
    match s with
    | existT _ ty i => single <$> trInst ty i
    end.

  Definition trRepeat n (c : list C.Ast.statement + {TranslationError}) :=
    match n with
    | 0 => {- [] -} (* TODO : Consider making this an error *)
    | 1 => c
    | _ => let cond := Expr.gt_zero repCtr in
           let decr := C.Ast.decrement repCtr in
           let loop n c := [ forLoop (init n) cond decr (Braces c) ] in
           loop n <$> c
    end.

End Internals.

Module Config <: CONFIG.

  Definition statement   := C.Ast.statement.
  Definition programLine := Ast.line.

  Definition typs := c_type_system.
  Definition vars := Internals.variables.

  Definition M : mSpecs verse_type_system :=
    {|
      mtypes        := c_type_system;
      mvariables    := Internals.variables;
      mtypeCompiler := verseTranslation Internals.trType Internals.trConst Internals.trOp
    |}.

  Definition target_semantics
    : Semantics M (list C.Ast.statement + {TranslationError})
    := Build_Semantics _ M (list C.Ast.statement + {TranslationError})
                       _ _ _ Internals.trStatement Internals.trRepeat.

  Definition streamOf {k}(block : type k)
    : typeOf c_type_system memory
    := let sz := match block with
                 | array b _ | ptrToArray b _ => b
                 | _ => 1
                 end in
       let ty0 := match block in type k0 return type direct with
                  | array _ t | ptrToArray _ t => t
                  | t => t
                  end in
       ptrToArray sz ty0.

  Definition dereference {k}{ty : type k}
    : vars (existT _ _ (streamOf ty)) -> vars (existT _ _ ty)
    :=  match ty with
       | ptrToArray b t => fun x => x (* this branch is not really used *)
       | _ => fun x => Expr.ptrDeref (Internals.blockPtr x)
       end.

  Definition mapOverBlocks {block : type memory}
             (stream : vars (existT _ _ (streamOf block)))
             (body : list statement)
             : list statement
    := (let cond := Expr.gt_zero (Internals.counter stream) in
        let actualBody :=  body ++
                                [ C.Ast.increment (Internals.blockPtr stream);
                                  C.Ast.decrement (Internals.counter stream)]

        in [ whileLoop cond (Braces actualBody) ]
       )%list.


  Fixpoint allocToList (st : Scope.type typs)
    :  Scope.allocation vars st -> list declaration :=
    match st as st0 return Scope.allocation vars st0 -> list declaration
    with
    | []      => fun _   => nil
    | _ :: xs => fun arg =>
                   let this := Internals.decl (hlist.hd arg) in
                   let rest := allocToList xs (hlist.tl arg) in
                   (this ++ rest)%list
    end.

  Arguments allocToList [st].

  Definition makeFunction (name : Set) (fname : name)(fsig : funSig typs vars)
             (body : list statement)
    := let ps := params (allocToList (Target.parameters fsig)) in
       let ls := List.map declareStmt (allocToList (Target.locals fsig)) in
       function fname ps (Braces (ls ++ body))%list.

End Config.
