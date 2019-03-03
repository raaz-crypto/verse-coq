Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import Verse.Syntax.
Require Import Verse.Language.Ast.
Require Import Verse.Language.Operators.
Require Import Verse.Error.

Require Import List.
Require Import Omega.
Import ListNotations.

Set Implicit Arguments.
(** * Notation and Pretty printing.


A user is expected to define a program by giving a list of
[instruction]s. Expressing instructions directly using the
constructors of the [arg] and [instruction] types can be painful. We
expose some convenient notations for simplifying this task. Note that
in the notations below, the operands of the instruction can either be
variables or constants or indexed arrays.

It is convenient to have a pretty printed syntax for instructions in
verse. We give a C-like pretty printing for verse instructions defined
over variables that can themselves be pretty printed.

*)




(* begin hide *)


Class LARG (v : VariableT)(k : kind)(ty : type k) t  := { toLArg : t -> arg v lval ty }.
Class RARG (v : VariableT)(k : kind)(ty : type k) t  := { toRArg : t -> arg v rval ty }.

Class IndexArg (Ix : Set)(result : Type) t
  := { deref : t -> Ix  -> result }.

Section ARGInstances.
  Variable v  : VariableT.
  Variable k  : kind.
  Variable ty : type k .

  Global Instance larg_of_argv : LARG v ty (arg v lval ty) := { toLArg := fun t => t} .
  Global Instance rarg_of_argv : RARG v ty (arg v rval ty) := { toRArg := fun t => t}.
  Global Instance larg_of_v    : LARG v ty (v ty)    := { toLArg := fun t => var t}.
  Global Instance rarg_of_v    : RARG v ty (v ty)    := { toRArg := fun t => var t}.


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

Global Instance const_arg_v (v : VariableT)(ty : type direct) : RARG v ty (Types.constant ty)
  := { toRArg := @const v ty }.

Global Instance nat_arg_v (v : VariableT)(ty : type direct) : RARG v ty nat
  := { toRArg := fun n => @const v ty (natToConstant ty n)}.

Global Instance N_arg_v (v : VariableT)(ty : type direct) : RARG v ty N
  := { toRArg := fun n => @const v ty (NToConstant ty n)}.
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


Ltac  verse_warn :=
  match goal with
  | [ |- ?T ] => idtac "verse: unable to dispose of" T
  end.

Ltac verse_bounds_warn := verse_warn; idtac "possible array index out of bounds".
Ltac verse_modulus_warn := verse_warn; idtac "possible modulo arithmetic over zero".

Global Hint Resolve NPeano.Nat.mod_upper_bound.

(* Typically verse throws up bound checks of the kind x < b where b is a symbolic array size

*)
Ltac verse_simplify := match goal with
                       | [ H : ?T |- ?T ]     => exact H
                       | [ |- _ <> _ ]        => unfold not; let H := fresh "H" in intro H; inversion H
                       | [ |- ?A mod ?B < ?B ] => apply (NPeano.Nat.mod_upper_bound A B)
                       | [ |- _ <= ?T         ] => compute; omega
                       | [ |- _ < ?T         ] => compute; omega
                       end.


Ltac verse_print_mesg :=  match goal with
                          | [ |- _ < _         ]  => verse_bounds_warn
                          | [ |- _ <= _         ] => verse_bounds_warn
                          | [ |- _ < _         ]  => verse_warn; idtac "possible array index out of bound"
                          | [ |- LARG _ _ _ _  ]  => idtac "verse: possible ill-typed operands in instructions"
                          | [ |- RARG _ _ _ _  ]  => idtac "verse: possible ill-typed operands in instructions"
                          | _                     => verse_warn; idtac "please handle these obligations yourself"
                          end.

Tactic Notation "verse" uconstr(B) := refine B; repeat verse_simplify; verse_print_mesg.


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
