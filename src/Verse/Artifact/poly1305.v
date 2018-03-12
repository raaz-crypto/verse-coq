Require Import Verse.
Require Import Verse.Semantics.
Require Import Verse.DecFacts.
Require Import Verse.Semantics.BoundSemantics.
Require Import Verse.Types.
Require Import Verse.Types.Internal.

Require Import List.
Import VectorNotations.

Notation SIZE := 5.

Inductive var : VariableT :=
| p : var _ Word64
| a0 : var _ Word64
| a1 : var _ Word64
| a2 : var _ Word64
| a3 : var _ Word64
| a4 : var _ Word64
| b0 : var _ Word64
| b51 : var _ Word64
| b52 : var _ Word64
| b53 : var _ Word64
| b54 : var _ Word64
| tmp : var _ Word64
.

Definition var_eqb k (ty : type k) (x y : var _ ty) : bool :=
  match x, y with
  | p, p
  | a0, a0 | a1, a1 | a2, a2 | a3, a3 | a4, a4
  | b0, b0
  | b51, b51 | b52, b52 | b53, b53 | b54, b54
  | tmp, tmp => true
  | _, _ => false
  end.

Definition polymul : code var.
  verse
    [ p ::== Ox "0000000000000000";
      tmp ::= a0 [*] b0;
      p ::=+ tmp;
      tmp ::= a1 [*] b54;
      p ::=+ tmp;
      tmp ::= a2 [*] b53;
      p ::=+ tmp;
      tmp ::= a3 [*] b52;
      p ::=+ tmp;
      tmp ::= a4 [*] b51;
      p ::=+ tmp
    ]%list.
Defined.

Import BoundSemantics.

Definition init : State var :=
  fun k (ty : type k) (v : var _ ty) =>
    match v in var _ ty0 return T.typeDenote ty0 + {VariableError var} with
    | a0 | a1 | a2 | a3 | a4 => {- (0, 31) -}
    | b0 => {- (0, 31) -}
    | b54 | b53 | b52 | b51 => {- (0, 31) -}
    | p => {- (0, 0) -}
    | tmp => {- (0, 0) -}
    end.

Definition finalS := (recover(codeDenote var_eqb init polymul)).
Compute (finalS _ _ p).
