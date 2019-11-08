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
Require Import Verse.Language.Ast.
Require Import Verse.Language.Types.
Require Import Verse.TypeSystem.
Require Import Verse.Variables.
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

* We have the class [EXPR] that declares instances which can be
  converted to [expr]. Some of the instances of this class are [v ty],
  [nat]'s and [expr]'s themselves.

* We use infix operators like [+] etc to combine instances of [EXPR]
  to get new expressions. Thus we can embed many of the common types
  as expressions.


*)

Section Embedding.
  Variable v  : Variables.U verse_type_system.
  Variable ty : type direct.

  (** Class of all types [t] that can be converted into expressions *)
  Global Class EXPR  t := { toExpr  : t -> expr v ty }.


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
  Global Class LEXPR t := { toLexpr : t -> lexpr v ty }.

  Global Instance lexpr_to_lexpr : LEXPR (lexpr v ty) := { toLexpr := fun t => t}.
  Global Instance v_to_lexp      : LEXPR (v ty)       := { toLexpr := fun x => var x }.



  (** We now define helper functions that "lift" verse operators to
      work with instances of [EXPR].  *)
  Section Operators.

    Variable bop    : op 2.
    Variable uop    : op 1.

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
      := app bop [toExpr e1 ; toExpr e2].

    (** Update instruction which uses an input binary operator to
        update the l-expression [x].  *)

    Definition binOpUpdate : statement v
      := existT _ _ (update (toLexpr lhs) bop [toExpr e1]).


    (** Applies the unary operator [o] to the value [e] that is
        convertible to expression. *)
    Definition uniOpApp
    :=  app uop [toExpr e1].

    (** Update a given lexpression using the given unary operator
        [o]. *)
    Definition uniOpUpdate : statement v
      := existT _ _ (update (toLexpr lhs) uop []).

    End Operators.
End Embedding.



Arguments assignStmt [v ty t] lhs [class t1] e1 [class1].
Arguments moveStmt [v ty t] lhs [class] x.
Arguments binOpApp [v ty] bop  [t1 t2] e1 e2  [class1 class2].
Arguments binOpUpdate [v ty] bop [t] lhs [class] [t1] e1 [class1] .
Arguments uniOpApp [v ty] uop  [t1] e1 [class1].
Arguments uniOpUpdate [v ty] uop [t] lhs [class].


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






Notation "A [- N -] " := (idx A (@exist _ _ N%nat _)) (at level 29).

(** Notation for operators.

We more or less follow the C convention for operator and their
precedence except for the operator [^] which has a predefined
precedence in Coq.

*)



Notation "'neg' E"  := (uniOpApp bitComp E)      (at level 30, right associativity).

Infix "*"           := (binOpApp mul)            (at level 40, left associativity).
Infix "/"           := (binOpApp quot)           (at level 40, left associativity).
Infix "%"           := (binOpApp rem)            (at level 40, left associativity).

Infix "+"           := (binOpApp plus)           (at level 50, left associativity).
Infix "-"           := (binOpApp minus)          (at level 50, left associativity).

Notation "E  <<  N" := (uniOpApp (shiftL N) E)   (at level 55, left associativity).
Notation "E  >>  N" := (uniOpApp (shiftR N) E)   (at level 55, left associativity).
Notation "E <<<  N" := (uniOpApp (rotL N)   E)   (at level 55, left associativity).
Notation "E >>>  N" := (uniOpApp (rotR N)   E)   (at level 55, left associativity).

Infix "&"           := (binOpApp bitAnd)         (at level 56, left associativity).
Infix "⊕"           := (binOpApp bitXor)         (at level 57, left associativity).
Infix "xor"         := (binOpApp bitXor)         (at level 57, left associativity, only parsing).
Infix "|"           := (binOpApp bitOr)          (at level 58, left associativity).


Infix "::="   := assignStmt           (at level 70).
Infix "<-"    := moveStmt             (at level 70).
Infix "::=+"  := (binOpUpdate plus)   (at level 70).
Infix "::=-"  := (binOpUpdate minus ) (at level 70).
Infix "::=*"  := (binOpUpdate mul   ) (at level 70).
Infix "::=/"  := (binOpUpdate quot  ) (at level 70).
Infix "::=%"  := (binOpUpdate rem   ) (at level 70).
Infix "::=|"  := (binOpUpdate bitOr ) (at level 70).
Infix "::=&"  := (binOpUpdate bitAnd) (at level 70).
Infix "::=x"  := (binOpUpdate bitXor) (at level 70, only parsing).
Infix "::=⊕"  := (binOpUpdate bitXor) (at level 70).

Notation "++ A"        := (increment (toLexpr A))      (at level 70).
Notation "-- A"        := (decrement (toLexpr A))      (at level 70).
Notation "A ::=<< N"   := (uniOpUpdate (shiftL N) A)   (at level 70).
Notation "A ::=>> N"   := (uniOpUpdate (shiftR N) A)   (at level 70).
Notation "A ::=<<< N"  := (uniOpUpdate (rotL N)   A)   (at level 70).
Notation "A ::=>>> N"  := (uniOpUpdate (rotR N)   A)   (at level 70).
Notation "'CLOBBER' A" := (existT _ _ (clobber A))     (at level 70).

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


(* ** Array like indexing.

One of the obvious things that

*)

(*

(* begin hide *)


Class LARG (v : VariableT)(k : kind)(ty : type k) t  := { toLArg : t -> arg v lval ty }.
Class RARG (v : VariableT)(k : kind)(ty : type k) t  := { toRArg : t -> arg v rval ty }.


Section ARGInstances.
  Variable v  : VariableT.
  Variable k  : kind.
  Variable ty : type k .



End ARGInstances.

Section Indexing.
  Variable v  : VariableT.
  Variable ty : type direct.
  Variable aK : argKind.
  Variable bound  : nat.
  Variable e  : endian.

  Global Instance index_array_var :
    IndexArg {i | i < bound} (arg v aK ty)(v (array bound e ty)) :=
    { deref := @index v aK bound e ty }.

  Check exist.
  Global Instance index_var_cache :
    IndexArg {i | i < bound} (v ty) (forall i,  i < bound -> v ty):=
    { deref := fun A ix =>  match ix with
                            | @exist _ _ i pf => A i pf
                            end}.
End Indexing.


(* end hide *)

Notation "A [- N -]"     := (deref A (@exist _ _ N%nat _)) (at level 29).

Notation "! A"           := (inst (index A 0 _)) (at level 70).
Notation "++ A"        := (inst (increment (toLArg A))) (at level 70).
Notation "-- A"        := (inst (decrement (toLArg A))) (at level 70).

Notation "A ::= B"      := (inst (assign (assign2 nop (toLArg A) (toRArg B)))) (at level 70, B at level 29).

Notation "A ::= B + C" := (inst (assign (assign3 plus  (toLArg A) (toRArg B) (toRArg C) )))  (at level 70, B at level 29).
Notation "A ::= B - C" := (inst (assign (assign3 minus (toLArg A) (toRArg B) (toRArg C))))  (at level 70, B at level 29).
Notation "A ::= B * C" := (inst (assign (assign3 mul   (toLArg A) (toRArg B) (toRArg C))))  (at level 70, B at level 29).
Notation "A ::= B / C" := (inst (assign (assign3 quot  (toLArg A) (toRArg B) (toRArg C))))  (at level 70, B at level 29).
Notation "A ::= B % C" := (inst (assign (assign3 rem   (toLArg A) (toRArg B) (toRArg C))))  (at level 70, B at level 29).
Notation "A ::= B | C" := (inst (assign (assign3 bitOr (toLArg A) (toRArg B) (toRArg C))))  (at level 70, B at level 29).
Notation "A ::= B & C" := (inst (assign (assign3 bitAnd (toLArg A) (toRArg B) (toRArg C))))  (at level 70, B at level 29).
Notation "A ::= B ^ C" := (inst (assign (assign3 bitXor (toLArg A) (toRArg B) (toRArg C))))  (at level 70, B at level 29).

Notation "A ::=+ B " := (inst (assign (update2 plus  (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::=- B " := (inst (assign (update2 minus (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::=* B " := (inst (assign (update2 mul   (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::=/ B " := (inst (assign (update2 quot  (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::=% B " := (inst (assign (update2 rem   (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::=| B " := (inst (assign (update2 bitOr (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::=& B " := (inst (assign (update2 bitAnd (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::=^ B " := (inst (assign (update2 bitXor (toLArg A) (toRArg B)))) (at level 70).

Notation "A ::=~ B "     := (inst (assign (assign2 bitComp    (toLArg A) (toRArg B)))) (at level 70).
Notation "A ::= B <<< N" := (inst (assign (assign2 (rotL N)   (toLArg A) (toRArg B)))) (at level 70, B at level 29).
Notation "A ::= B >>> N" := (inst (assign (assign2 (rotR N)   (toLArg A) (toRArg B)))) (at level 70, B at level 29).
Notation "A ::= B <<  N"  := (inst (assign (assign2 (shiftL N) (toLArg A) (toRArg B)))) (at level 70, B at level 29).
Notation "A ::= B >>  N" := (inst (assign (assign2 (shiftR N) (toLArg A) (toRArg B)))) (at level 70, B at level 29).
Notation "A ::=<< N "    := (inst (assign (update1 (shiftL N) (toLArg A)))) (at level 70).
Notation "A ::=>> N "    := (inst (assign (update1 (shiftR N) (toLArg A)))) (at level 70).
Notation "A ::=<<< N "    := (inst (assign (update1 (rotL N)  (toLArg A)))) (at level 70).
Notation "A ::=>>> N "    := (inst (assign (update1 (rotR N)  (toLArg A)))) (at level 70).

Notation "'CLOBBER' A"   := (inst (clobber A)) (at level 70). (* Check level *)
Notation "'MOVE'  B 'TO'   A [- N -]"       := (inst (moveTo A (@exist _ _ (N%nat) _) B)) (at level 200, A ident).


(** Notations for annotations in code *)

Class Context tyD v := val : @context tyD v * @context tyD v.

Notation "A 'HAD' X ; E" := (let X := (snd val) _ _ A in E)
                              (at level 81, right associativity, only parsing).


Notation "A 'HAD' X 'IN' E" := (let X := (snd val) _ _ A in E)
                             (at level 81, right associativity, only parsing).


Notation "'ASSERT' P" := (assert (fun s : Context _ _ => P)) (at level 100).

Notation "A 'HAS' X ; E"
  := (let X := (fst val) _ _ A in E)
       (at level 81, right associativity, only parsing).

Notation "A 'HAS' X 'IN' E"
  := (let X := (fst val) _ _ A in E)
       (at level 81, right associativity, only parsing).

Notation "'Val' X" := ((fst val) _ _ X) (at level 50).
Notation "'Old' X" := ((snd val) _ _ X) (at level 50).

(**

One another irritant in writing code is that the array indexing needs
proof that the bounds are not violated. We use the following tactic to
dispose off all such obligations.

*)


(* Local sample code to test error message
Section TypeError.

  Variable v : VariableT.
  Variable A : v direct Word64.
  Variable B : v direct Word32.
  Variable C : v memory (Array 42 bigE Word64).

  Definition badCode : code v.
    Debug Off.
    verse [A ::=  A [+] C[- (48 mod 42)%nat -] ]%list.

  Defined.

End TypeError.
*)

(* begin hide *)
Require Import Verse.PrettyPrint.
Section PrettyPrintingInstruction.

  (** The variable type for our instructions *)
  Variable v : VariableT.


  (** The pretty printing instance for our variable *)
  Variable vPrint : forall k (ty : type k), PrettyPrint (v ty).

  (** The pretty printing of our argument *)
  Fixpoint argdoc {aK}{k}(ty : type k ) (av : arg v aK ty) :=
    match av with
    | var v       => doc v
    | const c     => doc c
    | index v (@exist _ _ n _) => doc v <> bracket (decimal n)
    end.

  Global Instance arg_pretty_print : forall aK k (ty : type k), PrettyPrint (arg v aK ty)
    := { doc := @argdoc _ _ _ }.


  Definition opDoc {ar : arity}(o : op ar) :=
    match o with
    | plus     => text "+"
    | minus    => text "-"
    | mul      => text "*"
    | quot     => text "/"
    | rem      => text "%"
    | bitOr    => text "|"
    | bitAnd   => text "&"
    | bitXor   => text "^"
    | bitComp  => text "~"
    | rotL _   => text "<*<"
    | rotR _   => text ">*>"
    | shiftL _ => text "<<"
    | shiftR _ => text ">>"
    | nop      => text ""
    end.

  Definition EQUALS := text "=".
  Definition mkAssign {ar : arity}(o : op ar)   (x y z : Doc)  := x <_> EQUALS <_> y <_> opDoc o <_> z.
  Definition mkRot    {k}(ty : type k)(o : uniop) (x y : Doc)  :=
    let rotSuffix := match ty with
                     | word w     => decimal (2 ^ (w + 3))%nat
                     | multiword v w => text "V" <> decimal (2^v * 2^(w+3)) <> text "_" <> decimal (2^(w +3))
                     | _          => text "Unsupported"
                     end in
    match o with
    | rotL n => x <_> EQUALS <_> text "rotL" <> rotSuffix <> paren (commaSep [y ; decimal n])
    | rotR n => x <_> EQUALS <_> text "rotR" <> rotSuffix <> paren (commaSep [y ; decimal n])
    | _      => text "BadOp"
    end.

  Definition mkUpdate {a : arity}(o : op a) (x y   : Doc) := x <_> opDoc o <> EQUALS <_> y.
  Local Definition convertEndian e d :=
    match e with
    | bigE => text "bigEndian" <> paren d
    | littleE => text "littleEndian" <> paren d
    | _       => d
    end.

  Local Definition mkPair x y := paren (commaSep [x; y]).

  (** The pretty printing of assignment statements **)
  Global Instance assignment_pretty_print : PrettyPrint (assignment v)
    := { doc := fun assgn =>
                  match assgn with
                  | assign3 o x y z => mkAssign o (doc x) (doc y) (doc z)
                  | update2 o x y   => mkUpdate o (doc x) (doc y)
                  | @assign2 _ ty u x y   =>
                    match u with
                    | bitComp  | nop  => mkAssign u (doc x) empty (doc y)
                    | shiftL n | shiftR n  => mkAssign u (doc x) (doc y) (decimal n)
                    | rotL n   | rotR n    => mkRot ty u (doc x)(doc y)
                    end
                  | @update1 _ ty u x      =>
                    let xdoc := doc x in
                    match u with
                    | bitComp  | nop       => mkAssign u xdoc empty xdoc
                    | shiftL n | shiftR n  => mkUpdate u xdoc (decimal n)
                    | rotL n   | rotR n    => mkRot ty u xdoc xdoc
                    end
                  end
       }.

  Definition mkDouble {ar} (o : op ar) (x : Doc) := opDoc o <> opDoc o <> x.

  Global Instance instruction_pretty_print : PrettyPrint (instruction v)
    := { doc := fun i => match i with
                         | assign a => doc a
                         | increment a => mkDouble plus (doc a)
                         | decrement a => mkDouble minus (doc a)
                         | @moveTo  _ _ e _  a (@exist _ _ i _) b
                           => doc a <_> bracket (doc i) <_> EQUALS <_> convertEndian e (doc b)
                         | clobber v => text "CLOBBER" <_> doc v
                         end
       }.

End PrettyPrintingInstruction.

(* end hide *)


(** *** Illustrative example of the notation.

To demonstrate the use of this notation and its pretty printed form,
we first define an inductive type whose constructors are the variables
of our program.

*)

Module Demo.
  Inductive MyVar : VariableT :=
  |  X : MyVar Word8
  |  Y : MyVar Word64
  |  Z : MyVar (Vector128 Word32)
  |  A : MyVar (Array 42 bigE Word8)
  .



(**

To get the above program frgment pretty printed all we need is pretty
print instance for the variable type [MyVar].

*)


Instance PrettyPrintMyVar : forall k (ty : type k), PrettyPrint (MyVar ty) :=
  { doc := fun v => text ( match v with
                           | X => "X"
                           | Y => "Y"
                           | Z => "Z"
                           | A => "A"
                           end
                         )
  }.
  Import Vector.
  Import Vector.VectorNotations.
  Import Verse.Nibble.


  (**

For illustration consider the following (nonsensical) program
fragment.  Notice that we can directly use the variables (as in [X],
[Y], Z) or constants (the [Ox "..."] are appropriate constants) as
operands of the programming fragment.


   *)


  Definition vec_const : constant (Vector128 Word32) := [ Ox "12345678"; Ox "12345678"; Ox "12345678"; Ox "12345678"].

  Definition prog : code MyVar.
    verse [ X ::= X << 5 ;
            X ::=>> 5;
            X ::= X + (A[- 2 -]);
            X ::= X * Ox "55";
            Z ::= Z + vec_const;
            ++ Y
          ]%list.
   Defined.


  (** The above program fragment is pretty printable because the
      underlying variable type ([MyVar] in this case), is pretty printable
*)

End Demo.

*)