(* begin hide *)
Require Import Verse.BitVector.
Require Import BinNat.
Require Import Arith.
Require Import NArith.


Require Import Verse.Ast.
Require Import Verse.TypeSystem.
Require Import Verse.Language.Types.

Module Internals.

  Definition makeMask (mask : forall sz : nat,  Bvector sz) ty  : const ty :=
    let maskWord sz : const (word sz) := mask _ in
    match ty with
    | word sz => maskWord sz
    | multiword m sz => Vector.const (maskWord sz) (2^m)
    end.


  Definition selL n : forall ty : type direct, const ty :=
    makeMask (fun _ => BitVector.lower_ones  n).

  Definition selU n : forall ty : type direct, const ty :=
    makeMask (fun _ => BitVector.upper_ones  n).

  Definition selAt (pos : nat)(len : nat) : forall ty, const ty
    := makeMask (fun _ => BitVector.onesAt pos len).


  Definition clearL n : forall ty, const ty
    := makeMask (fun sz => let bsz := bitSize sz in
                        BitVector.upper_ones (bsz - n)).


  Definition clearU n : forall ty, const ty
    := makeMask (fun sz => let bsz := bitSize sz in
                        BitVector.lower_ones (bsz - n)).


  Definition selShiftR  n (ty : type direct) : nat
    := match ty with
       | word sz | multiword _ sz => bitSize sz - n
       end.
End Internals.

Require Import Verse.Language.Pretty.
(* end hide *)



(** * Keep and clear bits

The [keepOnlyLower n] ([keepOnlyUpper n]) keeps the lower
(respectively upper) bits of the given expression and clears all the
other bits.  Similarly [clearOnlyLower n] ([clearOnlyUpper n]) clears
the lower (respectively upper) bits while keeping the rest of the bits
intact.  If the expression is of type multiword, then the
keepOnly/clearOnly functions keeps or clears n bits from each of the
component of the multiword.

When selecting the top bits, there is also an additional option. We
shift out the bottom bits. We call this function the topBits function.
The difference is illustrated in the picture below.

 *)

(*

<<
     |---- top n-bits ---|--- lower bits---|
                         |
                      keepOnlyUpper
                         |
                         V
     |---- top n-bits ---|00000000000000000|



     |---- top n-bits ---|--- lower bits---|
                         |
                      toTopBits
                         |
                         V
     |00000000000000000|---- top n-bits ---|


>>


 *)

(** There is also the update version of these functions that updates a
    given l-expr with the above mentioned operations.  *)
Section ForAll.
  Open Scope verse_scope.
  Variable v : VariableT.
  Variable ty : type direct.
  Variable E  : Type.
  Variable E_is_Expr : Pretty.EXPR v ty E.
  Variable L  : Type.
  Variable L_is_Lexpr : Pretty.LEXPR v ty L.


  Definition keepOnlyLower       n (e:E) := [verse| e & `Internals.selL n ty`  |].
  Definition keepOnlyLowerUpdate n (l:L) := [verse| l &= `Internals.selL n ty` |].

  Definition clearOnlyLower       n (e:E) := [verse| e & `Internals.clearL n ty` |].
  Definition clearOnlyLowerUpdate n (l:L) := [verse| l &= `Internals.clearL n ty`|].


  Definition keepOnlyUpper       n (e:E) := [verse| e &  `Internals.selU n ty` |].
  Definition keepOnlyUpperUpdate n (l:L) := [verse| l &= `Internals.selU n ty` |].
  Definition toTopBits           n (e:E) := [verse| e >>  `Internals.selShiftR n ty`|].
  Definition toTopBitsUpdate     n (l:L) := [verse| l >>= `Internals.selShiftR n ty` |].

  Definition clearOnlyUpper       n (e:E) := [verse| e & `Internals.clearU n ty` |].
  Definition clearOnlyUpperUpdate n(l: L) := [verse| l &= `Internals.clearU n ty` |].



(* ** Efficient division modulo 2^n.

We can give efficient division algorithms when the divisor is a power of 2.

 *)


  Definition div2power_nat          n (e:E) := [verse| e >> n|].
  Definition div2powerUpdate_nat    n (l:L) := [verse| l >>= n |].
  Definition modulo2power_nat       := keepOnlyLower.
  Definition modulo2powerUpdate_nat := keepOnlyLowerUpdate.


End ForAll.

(* begin hide *)
Arguments keepOnlyLower [v ty E E_is_Expr].
Arguments keepOnlyLowerUpdate [v ty L L_is_Lexpr].

Arguments clearOnlyLower       [v ty E E_is_Expr].
Arguments clearOnlyLowerUpdate [v ty L L_is_Lexpr].


Arguments keepOnlyUpper       [v ty E E_is_Expr].
Arguments keepOnlyUpperUpdate [v ty L L_is_Lexpr].
Arguments toTopBits           [v ty E E_is_Expr].
Arguments toTopBitsUpdate     [v ty L L_is_Lexpr].

Arguments clearOnlyUpper       [v ty E E_is_Expr].
Arguments clearOnlyUpperUpdate [v ty L L_is_Lexpr].

Arguments div2power_nat        [v ty E E_is_Expr].
Arguments div2powerUpdate_nat  [v ty L L_is_Lexpr].
Arguments modulo2power_nat     [v ty E E_is_Expr].
Arguments modulo2powerUpdate_nat [v ty L L_is_Lexpr].
(* end hide *)
