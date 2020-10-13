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
  Class EXPR  t := { toExpr  : t -> expr v ty }.


  (** *** Instances of [EXPR]
   *)

  Global Instance expr_to_expr   : EXPR (expr  v ty)  := { toExpr := fun t => t}.
  Global Instance v_to_exp       : EXPR (v ty)        := { toExpr := fun x => valueOf (var x)}.
  Global Instance lexp_to_exp    : EXPR (lexpr v ty)  := { toExpr := fun x => valueOf x}.
  Global Instance const_to_expr  : EXPR (const ty)    := { toExpr := fun c => cval c }.
  Global Instance nat_to_exp     : EXPR nat
  := { toExpr := fun n => cval (natToConst ty n)}.

  Global Instance N_to_exp       : EXPR N
  := { toExpr := fun n => cval (NToConst ty n)}.

  (** Class similar to [EXPR] but creates l-expressions *)
  Class LEXPR t := { toLexpr : t -> lexpr v ty }.

  Global Instance lexpr_to_lexpr : LEXPR (lexpr v ty) := { toLexpr := fun t => t}.
  Global Instance v_to_lexp      : LEXPR (v ty)       := { toLexpr := fun x => var x }.



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

     Definition moveStmt (x : v ty) : statement v
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

Instance bvec_to_expr v sz : EXPR v (word sz) (BWord sz)
  := { toExpr := fun v : const (word sz) => cval v }.
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
  := { idx : t -> Ix  -> result }.

Instance indexing_by_function b t : INDEXING {i | i < b} t (forall i : nat, i < b -> t) :=
  { idx := fun f ix => match ix with
                   | @exist _ _ i pf => f i pf
                   end
  }.

Instance array_indexing v ty b e : INDEXING {i | i < b}
                                            (lexpr v ty)
                                            (v memory (array b e ty))
  := { idx := fun a ix =>  deref a ix }.



Declare Scope verse_scope.
Delimit Scope verse_scope with verse.

Notation "A [- N -] " := (idx A (@exist _ _ N%nat _)) (at level 29) : verse_scope.

(** Notation for operators.

We more or less follow the C convention for operator and their
precedence except for the operator [^] which has a predefined
precedence in Coq.

*)


Notation "'neg' E"  := (uniOpApp bitComp E)      (at level 30, right associativity) : verse_scope.

Infix "*"           := (binOpApp mul)            (at level 40, left associativity)  : verse_scope.
Infix "/"           := (binOpApp quot)           (at level 40, left associativity)  : verse_scope.
Infix "%"           := (binOpApp rem)            (at level 40, left associativity)  : verse_scope.

Infix "+"           := (binOpApp plus)           (at level 50, left associativity) : verse_scope.
Infix "-"           := (binOpApp minus)          (at level 50, left associativity) : verse_scope.

Notation "E  <<  N" := (uniOpApp (shiftL N) E)   (at level 55, left associativity) : verse_scope.
Notation "E  >>  N" := (uniOpApp (shiftR N) E)   (at level 55, left associativity) : verse_scope.
Notation "E <<<  N" := (uniOpApp (rotL N)   E)   (at level 55, left associativity) : verse_scope.
Notation "E >>>  N" := (uniOpApp (rotR N)   E)   (at level 55, left associativity) : verse_scope.

Infix "AND"         := (binOpApp bitAnd)         (at level 56, left associativity) : verse_scope.
Infix "⊕"           := (binOpApp bitXor)         (at level 57, left associativity) : verse_scope.
Infix "XOR"         := (binOpApp bitXor)
                         (at level 57, left associativity, only parsing) : verse_scope.
Infix "OR"          := (binOpApp bitOr)          (at level 58, left associativity) : verse_scope.

Infix "::="   := assignStmt           (at level 70) : verse_scope.
Infix "<-"     := moveStmt             (at level 70) : verse_scope.
Infix "::=+"  := (binOpUpdate plus)   (at level 70) : verse_scope.
Infix "::=-"  := (binOpUpdate minus ) (at level 70) : verse_scope.
Infix "::=*"  := (binOpUpdate mul   ) (at level 70) : verse_scope.
Infix "::=/"  := (binOpUpdate quot  ) (at level 70) : verse_scope.
Infix "::=%"  := (binOpUpdate rem   ) (at level 70) : verse_scope.
Infix "::=|"  := (binOpUpdate bitOr ) (at level 70) : verse_scope.
Infix "::=&"  := (binOpUpdate bitAnd) (at level 70) : verse_scope.
Infix "::=x"  := (binOpUpdate bitXor) (at level 70, only parsing) : verse_scope.
Infix "::=⊕"  := (binOpUpdate bitXor) (at level 70) : verse_scope.

Notation "A ::=<< N"   := (uniOpUpdate (shiftL N) A)   (at level 70) : verse_scope.
Notation "A ::=>> N"   := (uniOpUpdate (shiftR N) A)   (at level 70) : verse_scope.
Notation "A ::=<<< N"  := (uniOpUpdate (rotL N)   A)   (at level 70) : verse_scope.
Notation "A ::=>>> N"  := (uniOpUpdate (rotR N)   A)   (at level 70) : verse_scope.
Notation "'CLOBBER' A" := (existT _ _ (clobber A))     (at level 70) : verse_scope.

Notation "'MOVE' B 'TO' A [- N -]"
  := (existT _ _ (moveTo (deref A (exist _ (N%nat) _)) B)) (at level 200, A ident) : verse_scope.

(* We overload notations for `instruction` and `line` *)
Declare Scope code_scope.
Delimit Scope code_scope with code.

Notation "A ::= E" := (instruct (assignStmt A E))  (at level 70) : code_scope.
Notation "A <- B" := (instruct (moveStmt A B)) (at level 70) : code_scope.
Notation "A ::=+ B" := (instruct (binOpUpdate plus A B)) (at level 70) : code_scope.
Notation "A ::=- B" := (instruct (binOpUpdate minus A B)) (at level 70) : code_scope.
Notation "A ::=* B" := (instruct (binOpUpdate mul A B)) (at level 70) : code_scope.
Notation "A ::=/ B" := (instruct (binOpUpdate quot A B)) (at level 70) : code_scope.
Notation "A ::=% B" := (instruct (binOpUpdate rem A B)) (at level 70) : code_scope.
Notation "A ::=| B" := (instruct (binOpUpdate bitOr A B)) (at level 70) : code_scope.
Notation "A ::=& B"  := (instruct (binOpUpdate bitAnd A B)) (at level 70) : code_scope.
Notation "A ::=x B"  := (instruct (binOpUpdate bitXor A B)) (at level 70, only parsing) : code_scope.
Notation "A ::=⊕ B" := (instruct (binOpUpdate bitXor A B)) (at level 70) : code_scope.

Notation "A ::=<< N"   := (instruct (uniOpUpdate (shiftL N) A))   (at level 70) : code_scope.
Notation "A ::=>> N"   := (instruct (uniOpUpdate (shiftR N) A))   (at level 70) : code_scope.
Notation "A ::=<<< N"  := (instruct (uniOpUpdate (rotL N)   A))   (at level 70) : code_scope.
Notation "A ::=>>> N"  := (instruct (uniOpUpdate (rotR N)   A))   (at level 70) : code_scope.
Notation "'CLOBBER' A" := (instruct (existT _ _ (clobber A)))     (at level 70) : code_scope.

Notation "'MOVE' B 'TO' A [- N -]"
  := (instruct (existT _ _ (moveTo (deref A (exist _ (N%nat) _)) B))) (at level 200, A ident) : code_scope.


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

Global Hint Resolve PeanoNat.Nat.mod_upper_bound.

(* Typically verse throws up bound checks of the kind x < b where b is a symbolic array size

 *)
Require Import Omega.

Ltac verse_simplify := match goal with
                       | [ H : ?T |- ?T ]     => exact H
                       | [ |- _ <> _ ]        => unfold not; let H := fresh "H" in intro H; inversion H
                       | [ |- ?A mod ?B < ?B ] => apply (PeanoNat.Nat.mod_upper_bound A B)
                       | [ |- _ <= ?T         ] => compute; omega
                       | [ |- _ < ?T         ] => compute; omega
                       end.


Ltac verse_print_mesg :=  match goal with
                          | [ |- _ < _         ]  => verse_bounds_warn
                          | [ |- _ <= _         ] => verse_bounds_warn
                          | [ |- _ < _         ]  => verse_warn; idtac "possible array index out of bound"
                          | [ |- LEXPR _ _ _   ]  => idtac "verse: possible ill-typed operands in instructions"
                          | [ |- EXPR _ _ _    ]  => idtac "verse: possible ill-typed operands in instructions"
                          | _                    => verse_warn; idtac "please handle these obligations yourself"
                          end.

Tactic Notation "verse" uconstr(B) := refine B; repeat verse_simplify; verse_print_mesg.
