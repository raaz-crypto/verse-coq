(** * Notation and Pretty printing.

Programs are essentially just values of type [code] and one can
construct these objects by applying the appropriate
constructors. Often these constructors are designed so that the
underlying program construct is _correct by construction_ --- for
example array indexing requires a proof that the index is smaller than
the array bound. This is achieved by there being additional parameters
to the constructor which are proofs of safety.

Creating such objects explicitly by applying constructors can be
painful. This module gives a set of Notations that makes the surface
syntax of these code values palatable to the user.

*)

Require Import NArith.
Require Import Nat.
Require Import Verse.Ast.
Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Import List.ListNotations.
Require        Vector.
Import         Vector.VectorNotations.
Require Import Verse.Nibble.

Set Implicit Arguments.


(* DEVELOPER notes.

We can avoid all type classes and move over to canonical structures if
that is what we are going to use in the rest of the code

*)


(** * Types embeddable as expressions

For program variables [v : VariableT] and a verse type [ty] recall
that [expr v ty] type captures expressions in verse. We would like to
consider other types like, [nat] constants, program variables [x : v ty]
etc, to be considered as verse expressions. We do this in two stages.

- We have the class [EXPR] that declares instances which can be
  converted to [expr]. Some of the instances of this class are [v ty],
  [nat]'s and [expr]'s themselves.

- We use infix operators like [+] etc to combine instances of [EXPR]
  to get new expressions. Thus we can embed many of the common types
  as expressions.


*)

Section Embedding.
  Variable v  : Variables.U verse_type_system.
  Variable ty : type direct.

  (** Class of all types [t] that can be converted into expressions *)
  Class EXPR  t := toExpr  : t -> expr v of type ty.


  (** *** Instances of [EXPR]
   *)

  #[export] Instance expr_to_expr   : EXPR (expr  v of type ty)  := @id _.
  #[export] Instance v_to_exp       : EXPR (v of type ty)        := fun x => valueOf (var x).
  #[export] Instance lexp_to_exp    : EXPR (lexpr v of type ty)  := valueOf (ty := existT _ _ ty).
  #[export] Instance const_to_expr  : EXPR (const ty)    := cval (ty:=ty).
  #[export] Instance nat_to_exp     : EXPR nat := fun n => cval (natToConst ty n).

  #[export] Instance N_to_exp       : EXPR N := fun n => cval (NToConst ty n).

  (** Class similar to [EXPR] but creates l-expressions *)
  Class LEXPR t := toLexpr : t -> lexpr v of type ty.

  #[export] Instance lexpr_to_lexpr : LEXPR (lexpr v of type ty) := @id _.
  #[export] Instance v_to_lexp      : LEXPR (v of type ty)       := var (ty:=ty).



  (** We now define helper functions that "lift" verse operators to
      work with instances of [EXPR].  *)
  Section Operators.

    Variable bop : operator verse_type_system ty 2.
    Variable uop : operator verse_type_system ty 1.

    Variable t      : Type.
    Variable lhs    : t.
    Variable class  : LEXPR t.


    Variable t1 t2 : Type.
    Variable e1 : t1.
    Variable e2 : t2.
    Variable class1 : EXPR t1.
    Variable class2 : EXPR t2.

    Definition assignStmt : statement v
      := existT _  _ (assign  (toLexpr lhs)  (toExpr e1)).

     Definition moveStmt (x : v of type ty) : statement v
      := existT _ _ (Ast.moveTo (toLexpr lhs) x).

    (** Applies the binary operator [o] to two values [e1] and [e2]
        both of which are convertable to expressions.  *)
    Definition binOpApp
      := binOp bop (toExpr e1) (toExpr e2).

    (** Update instruction which uses an input binary operator to
        update the l-expression [x].  *)

    Definition binOpUpdate : statement v
      := existT _ _ (binopUpdate (toLexpr lhs) bop (toExpr e1)).


    (** Applies the unary operator [o] to the value [e] that is
        convertible to expression. *)
    Definition uniOpApp
    :=  uniOp uop (toExpr e1).

    (** Update a given lexpression using the given unary operator
        [o]. *)
    Definition uniOpUpdate : statement v
      := existT _ _ (uniopUpdate (toLexpr lhs) uop).

    End Operators.
End Embedding.

#[export]
 Instance bvec_to_expr v sz : EXPR v (word sz) (BWord sz)
  := { toExpr := fun v : const (word sz) => cval v }.

#[export]
 Instance nibbles_to_exp v sz  : EXPR v (word sz) (Nibble.bytes (2^sz))
  := { toExpr := fun nibs => toExpr (toBv nibs) }.


Arguments assignStmt [v ty t] lhs [class t1] e1 {class1}.
Arguments moveStmt [v ty t] lhs [class] x.
Arguments binOpApp [v ty] bop  [t1 t2] e1 e2  {class1 class2}.
Arguments binOpUpdate [v ty] bop [t] lhs [class] [t1] e1 {class1} .
Arguments uniOpApp [v ty] uop  [t1] e1 {class1}.
Arguments uniOpUpdate [v ty] uop [t] lhs {class}.


(** * Indexing types.

Often we want to index elements withing a bound. The class [INDEXING]
captures such types. Array variables are usual objects but we have an
instance for generic indexing functions. The indexing functions
give

*)

Class INDEXING (Ix : Set)(result : Type) t
  := idx : t -> Ix  -> result.

#[export]
 Instance indexing_by_function b t : INDEXING {i | i < b} t (forall i : nat, i < b -> t)
  := fun f ix => match ix with
              | @exist _ _ i pf => f i pf
              end.

#[export]
 Instance array_indexing v ty b e : INDEXING {i | i < b}
                                            (lexpr v of type ty)
                                            (v of type (array b e ty))
  := fun a ix =>  deref a ix.

#[export]
 Instance vector_indexing A b : INDEXING {i | i < b} A (Vector.t A b) :=
  fun va ix => Vector.nth_order va (proj2_sig ix).
(*
Instance var_array (v : Variables.U verse_type_system) ty b : INDEXING {i | i < b}
                                                                       (v ty)
                                                                       (Vector.t (v ty) b)
  := fun va ix => Vector.nth_order va (proj2_sig ix).
*)

Class AST_maps (A B : Type) := { CODE : A -> list B }.

#[export] Instance code_id (v : VariableT)
  : AST_maps (code v) (statement (ts := verse_type_system) v) | 0
  := { CODE := id }.

#[export] Instance code_repeat (v : VariableT)
  : AST_maps (code v) (repeated (code (ts := verse_type_system) v)) | 1
  := { CODE := fun C => [ repeat 1 C ]%list }.

Declare Custom Entry verse.
(* Notation "'[code|' e  '|]'" := e (e custom verse). *)
Notation "A [ N ] " := (idx A (@exist _ _ N%nat _)) (in custom verse at level 29, N constr).
Notation "[verse| e |]" := e (e custom verse).
Notation "[code| x ; .. ; y |]":= (CODE (cons x .. (cons y nil) ..)) (x custom verse, y custom verse,
                                      format "[code| '[    '  '//' x ; '//' .. ; '//' y '//' ']' '//' '|]'"
                                    ).
Notation "x" := x (in custom verse at level 0, x global).
Notation "( x )" := x  (in custom verse at level 0).
Notation "` x `" := x  (in custom verse at level 0, x constr, format "` x `").


(** Notation for operators.

We more or less follow the C convention for operator and their
precedence except for the operator [^] which has a predefined
precedence in Coq.

*)


Notation "~ E"      := (uniOpApp bitComp E)      (in custom verse at level 30, right associativity).

Infix "*"           := (binOpApp mul)            (in custom verse at level 40, left associativity).
Infix "/"           := (binOpApp quot)           (in custom verse at level 40, left associativity).
Infix "%"           := (binOpApp rem)            (in custom verse at level 40, left associativity).

Infix "+"           := (binOpApp plus)           (in custom verse at level 50, left associativity).
Infix "-"           := (binOpApp minus)          (in custom verse at level 50, left associativity).

Notation "E  <<  N" := (uniOpApp (shiftL N) E)   (in custom verse at level 54, left associativity).
Notation "E  ≪  N" := (uniOpApp (shiftL N) E)   (in custom verse at level 54, left associativity).

Notation "E  >>  N" := (uniOpApp (shiftR N) E)   (in custom verse at level 54, left associativity).
Notation "E  ≫  N" := (uniOpApp (shiftR N) E)   (in custom verse at level 54, left associativity).

Notation "E <<<  N" := (uniOpApp (rotL N)   E)   (in custom verse at level 54, left associativity).
Notation "E ⋘  N" := (uniOpApp (rotL N)   E)   (in custom verse at level 54, left associativity).


Notation "E >>>  N" := (uniOpApp (rotR N)   E)   (in custom verse at level 54, left associativity).
Notation "E ⋙  N" := (uniOpApp (rotR N)   E)   (in custom verse at level 54, left associativity, N constr).

Infix "&"         := (binOpApp bitAnd)         (in custom verse at level 56, left associativity).
Infix "⊕"         := (binOpApp bitXor)         (in custom verse at level 57, left associativity).
Infix "^"         := (binOpApp bitXor)
                         (in custom verse at level 57, left associativity, only parsing).
Infix "|"         := (binOpApp bitOr)          (in custom verse at level 59, left associativity).

Infix ":="  := assignStmt           (in custom verse at level 70).
Infix "<-"   := moveStmt             (in custom verse at level 70).
Infix "+="  := (binOpUpdate plus)   (in custom verse at level 70).
Infix "-="  := (binOpUpdate minus ) (in custom verse at level 70).
Infix "*="  := (binOpUpdate mul   ) (in custom verse at level 70).
Infix "/="  := (binOpUpdate quot  ) (in custom verse at level 70).
Infix "%="  := (binOpUpdate rem   ) (in custom verse at level 70).
Infix "|="  := (binOpUpdate bitOr ) (in custom verse at level 70).
Infix "&="  := (binOpUpdate bitAnd) (in custom verse at level 70).
Infix "^="  := (binOpUpdate bitXor) (in custom verse at level 70, only parsing).
Infix "⊕="  := (binOpUpdate bitXor) (in custom verse at level 70).

Notation "A <<= N"   := (uniOpUpdate (shiftL N) A)   (in custom verse at level 70).
Notation "A ≪= N"   := (uniOpUpdate (shiftL N) A)   (in custom verse at level 70).

Notation "A >>= N"   := (uniOpUpdate (shiftR N) A)   (in custom verse at level 70).
Notation "A ≫= N"   := (uniOpUpdate (shiftR N) A)   (in custom verse at level 70).

Notation "A <<<= N"  := (uniOpUpdate (rotL N)   A)   (in custom verse at level 70).
Notation "A ⋘= N"  := (uniOpUpdate (rotL N)   A)   (in custom verse at level 70).

Notation "A >>>= N"  := (uniOpUpdate (rotR N)   A)   (in custom verse at level 70).
Notation "A ⋙= N"  := (uniOpUpdate (rotR N)   A)   (in custom verse at level 70, N constr).

Notation "'CLOBBER' A" := (existT _ _ (clobber A))   (in custom verse at level 70).
(*
Notation "'MOVE' B 'to' A [ N ]"
  := (existT _ _ (moveTo (deref A (exist _ (N%nat) _)) B)) (in custom verse at level 200, A ident).
 *)

(** * The verse tactic.

The notations clean up the surface syntax but it still leaves routine
but tedious proof burden on to the shoulders of the programmer. We
dispose this of using the tactic called verse. Usually this is the
proof obligations that come out of array indexing. The verse tatic
disposes it of and raises a warning when it cannot (usually these are
out of bound array access).

*)

Ltac  verse_warn :=
  match goal with
  | [ |- ?T ] => idtac "verse: unable to dispose of" T
  end.

Ltac verse_bounds_warn := verse_warn; idtac "possible array index out of bounds".
Ltac verse_modulus_warn := verse_warn; idtac "possible modulo arithmetic over zero".

(* The following doesn't seem to be used any more. Retained to bugfix a later realization. *)
(*Global Hint Resolve PeanoNat.Nat.mod_upper_bound.*)

(* Typically verse throws up bound checks of the kind x < b where b is a symbolic array size

 *)
Require Import Psatz.

Ltac verse_simplify := match goal with
                       | [ H : ?T |- ?T ]     => exact H
                       | [ |- _ <> _ ]        => unfold not; let H := fresh "H" in intro H; inversion H
                       | [ |- ?A mod ?B < ?B ] => apply (PeanoNat.Nat.mod_upper_bound A B)
                       | [ |- _ <= ?T         ] => compute; solve [repeat constructor | lia]
                       | [ |- _ < ?T         ] => compute; solve [repeat constructor | lia]
                       end.


Ltac verse_print_mesg :=  match goal with
                          | [ |- _ < _         ]  => verse_bounds_warn
                          | [ |- _ <= _         ] => verse_bounds_warn
                          | [ |- _ < _         ]  => verse_warn; idtac "possible array index out of bound"
                          | [ |- LEXPR _ _ _   ]  => idtac "verse: possible ill-typed operands in instructions"
                          | [ |- EXPR _ _ _    ]  => idtac "verse: possible ill-typed operands in instructions"
                          | _                    => verse_warn; idtac "please handle these obligations yourself"
                          end.

Ltac verse_crush := repeat verse_simplify; verse_print_mesg.
Tactic Notation "verse" uconstr(B) := refine B; verse_crush.
