(** * Bound semantics for correctness of Poly1305.

Poly1305 is a high speed message authentication primitive
<https://en.wikipedia.org/wiki/Poly1305> which makes use of finite
field arithmetic over the finite field F = GF(2^130 - 5). In this
sample code, we demonstrate how one can use the bound semantics to
verify correctness of the portions that implement this arithmetic on a
64-bit machine.

Arithmetic over the field F the integer arithmetic done modulo the
prime 2^130 - 5. One can think of these elements as bit vectors of
size 130 bits. Implementations of poly1305 on 64-bit machines store
store these 130-bit words in 5x64-bit variables each containing
26-bits of the original word. The extra 36 bits in each of these
variables is meant to hold the overflow when performing arithmetic
operations.


*)

Require Import Verse.

(** ** The program variables.

Consider two elements [a] and [b] in the field represented via
5x64-bit words each of 26-bit each [a0,...,a4] and [b0,...,b4]
respectively. Computing [a * b] in [F] results in 5x64-bit elements.
[p0,...,p4]. In this file we only consider the correctness in the
evaluation of p0. Let us first define our program variables for this.

*)
Inductive var : VariableT :=
| p0 : var _ Word64
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
  | p0, p0
  | a0, a0 | a1, a1 | a2, a2 | a3, a3 | a4, a4
  | b0, b0
  | b51, b51 | b52, b52 | b53, b53 | b54, b54
  | tmp, tmp => true
  | _, _ => false
  end.

Require Import Verse.Semantics.
Require Import Verse.DecFacts.
Require Import Verse.Semantics.BoundSemantics.
Require Import Verse.Types.
Require Import Verse.Types.Internal.
Require Import List.
Import VectorNotations.
Notation SIZE := 5.


(**

The formula for the [p0,...,p4] is given below

<<

p0 = a0*b0                                    + 5 * ( a1*b4 + a2*b3 + a3*b2 + a4*b1);
p1 = a0*b1 + a1*b0                            + 5 * ( a2*b4 + a3*b3 + a4*b2 );
p2 = a0*b2 + a1*b1 + a2*b0                    + 5 * ( a3*b4 + a4*b3 );
p3 = a0*b3 + a1*b2 + a2*b1 + a3*b0            + 5 * ( a4*b54 );
p4 = a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 ;

>>

 *)

(**

Note that the first few terms (printed left aligned) are the usual
terms that arise in the multiplication of

<< a = a0 + 2^26 * a1 + ... + 2^(104) a4 >>

<< b = b0 + 2^26 * b1 + ... + 2^(104) b4 >>


The additional terms that are of the form (5 * (...) ) arise because
2^130 is 5 in the field F.  We refer to the blog post of
<http://loup-vaillant.fr/tutorials/poly1305-design> for details.

*)

Definition polymul : code var.
  verse
    [ p0 ::== Ox "0000000000000000";
      tmp ::= a0 [*] b0;
      p0 ::=+ tmp;
      tmp ::= a1 [*] b54;
      p0 ::=+ tmp;
      tmp ::= a2 [*] b53;
      p0 ::=+ tmp;
      tmp ::= a3 [*] b52;
      p0 ::=+ tmp;
      tmp ::= a4 [*] b51;
      p0 ::=+ tmp
    ]%list.
Defined.

Import BoundSemantics.

Definition init : State var :=
  fun k (ty : type k) (v : var _ ty) =>
    match v in var _ ty0 return T.typeDenote ty0 + {VariableError var} with
    | a0 | a1 | a2 | a3 | a4 => {- (0, 26) -}
    | b0 => {- (0, 26) -}
    | b54 | b53 | b52 | b51 => {- (0, 29) -}
    | p0 => {- (0, 0) -}
    | tmp => {- (0, 0) -}
    end.

Definition finalS := (recover(codeDenote var_eqb init polymul)).

Compute (finalS _ _ p0).

(**

This computation gives the following response

<<
     = {-(0, 59) -}
     : T.typeDenote Word64 + {VariableError var}
>>
 *)

(**

What this means is that p0 has an upper bound of 2^59 and that none of
the arithmetic operations have overflowed.


*)
