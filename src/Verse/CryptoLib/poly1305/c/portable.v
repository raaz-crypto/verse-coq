Require Import Verse.
Require Vector.
Import VectorNotations.

(** For this module we use [P] to denote the prime 2^130 - 5, the
prime associated with Poly1305.


 *)
Require Import Semantics.NSemantics.
Import NSemanticsTactics.
Import NArith.
Module Internal.

  Section Poly1305.
    (** * Poly1305 on R,K

        Fix P to be the prime 2^130 - 5.  Let M be the message. By
        chunking into blocks of 128-bit each of which is thought of as
        elements of GF(P)[X], the message becomes a polynomial [ M(X)
        = C_1 X^t + C_2 X^(t - 1) ... C_t X + K]. The mac associated
        with this message is M(R) mod P rounded to 128 bits. We use
        the Horner's rule. We keep an accumulator A which is updated
        according to A := (A + C_i) * R

     *)


    Definition Word := Word64.
    Definition BLOCK_SIZE := 2.
    Definition Block := Array BLOCK_SIZE littleE Word.

     (** ** Keeping track of carry.

         Elements of the field GF(P) are 130 bits long. To avoid
         overflows when doing arithmetic, we keep track of such
         elements using five 64-bit variables, each of them carrying a
         payload of 26-bits each.  Let {x0,x1,x2,x3,x4} be such a
         variable set, the integer value associated with it is given
         by x0 + 2^26 x1 + 2^52 x2 + 2^78 x3 + 2^104 x4.

         We define the word size for this primitive as Word64 and the
         message as block of 2.  *)

    Definition GFP1305 := Array 5 hostE Word.
    Definition MASK26  : constant Word  := Ox "00:00:00:00 03:FF:FF:FF".
    Definition TwoPow25 : constant Word := Ox "00:00:00:00 01:00:00:00".
    Definition Five     : constant Word := Ox "00:00:00:00 00:00:00:05".
    Definition Zero     : constant Word := Ox "00:00:00:00 00:00:00:00".

    Variable progvar : VariableT.
    Arguments progvar [k] _.


    (** The parameters R and K and A are kept in their  GFP form *)

    Variable A : progvar GFP1305.
    Variable R : progvar GFP1305.
    Variable K : progvar GFP1305.

    (** We need a register copy of them *)
    Variable a0 a1 a2 a3 a4 : progvar Word.
    Definition accumulator := [a0 ; a1; a2 ; a3; a4]%vector.
    Definition ACC : VarIndex progvar 5 Word := varIndex accumulator.

    Variable r0 r1 r2 r3 r4 : progvar Word.
    Definition rs := [r0 ; r1;  r2 ; r3 ; r4]%vector.
    Definition Rs : VarIndex progvar 5 Word := varIndex rs.

    Variable p0 p1 p2 p3 p4 : progvar Word.
    Variable temp           : progvar Word.

    Definition CLEAR_ACC : code progvar.
      verse (foreach (indices A) (fun i iproff => [ ACC i _ ::==  Ox "00:00:00:00 00:00:00:00"]%list)).
    Defined.

    (** The variables to keep track of the coefficient of the
        polynomial
     *)



    Variable c0 c1 c2 c3 c4 : progvar Word.
    Definition C : VarIndex progvar 5 Word := varIndex [c0; c1; c2; c3; c4].

    (** This function loads 128 bit into the coefficient variables
        26-bit at a time. To avoid using additional variables. We will
        need to shift around bits and mask them. The first three
        coefficients [c0], [c1], and [c2] account for 78 bits. So we
        can manage this operation without any temporary variables by
        use the higher words, [c3] and [c4].

     *)

    Definition NVal (x0 x1 x2 x3 x4 : N) := (x0 + 2^26 * x1 + 2^52 * x2 + 2^78 * x3  + 2^104 * x4)%N.
    Definition LOAD_COEFFICIENT (blk : progvar Block) : code progvar.
      verse [
          c3 ::== blk [- 0 -];
          c4 ::== blk [- 1 -];
          (**
              All the 128 bits are now in the register combination
              [c3]:[c4]. Start by transferring the lowest 26 bits to
              c0
           **)
          c0 ::= c3 [&] MASK26;

          (**  Having given out 26 bits, we transfer the next 26 bits to c2 *)
          c3 ::=>> 26;
          c1 ::= c3 [&] MASK26;

         (** Shifting 26-positions once more, we have a total of 12
             bits in c3 that belongs to c2. First transfer this to c2
             and then use c3 as a temporary variable to transfer the
             remaining 14 bits from c4. We just need to shift c4 left
             by 12 and mask the bits.
          *)

          c2 ::= c3 >> 26;
          c3 ::= c4 << 12;
          c3 ::=& MASK26;
          c2 ::=| c3;

          (** Remove the 14-bits transferred to c2 and make it to get the bits of c3 *)
          c4 ::=>>14;
          c3 ::=  c4 [&] MASK26;

          (** The remaining 24 bit is what c4 deserves to get *)
          c4 ::=>> 26;
          ASSERT c3 HAD a0; c4 HAD a1;
                 c0 HAS x0;
                 c1 HAS x1;
                 c2 HAS x2;
                 c3 HAS x3;
                 c4 HAS x4
                    IN
                 (2^64 * a1 + a0 = NVal x0 x1 x2 x3 x4)%N ;
          c4 ::=| TwoPow25
        ]%list.
      Defined.
      (** Perform A += C *)
      Definition APLUSC : code progvar.
        verse (foreach (indices A) ( fun i ip => [ACC i _ ::=+ C i _]%list)).
      Defined.

      (** * Multiply by R.

         We think of the R's and A's as numbers in base 2^26. I.e

       *)
      (*
         <<
         A =  a0 + a1 X + a2 X^2 + a3 X^3 + a4 X^4
         R =  r0 + r1 X + r2 X^2 + r3 X^3 + r4 X^4
         >>

       *)

      (* If you multiply this as polynomials this would have 9
         coefficients. But notice that X = 2^26 and hence X^5 = 5 mod
         2^130 - 5. So the result can be seen as a coefficient X^(5+i)
         would become 5 X^i.

         This will give the following expression.

       *)
      (**
          <<
          p0 = a0 r0                                  + (a1 r4 + a2 r3 + a3 r2 + a4 r1) * 5
          p1 = a0 r1 + a1 r0                          + (a2 r4 + a3 r3 + a4 r2) * 5
          p2 = a0 r2 + a1 r1 + a2 r0                  + (a3 r4 + a4 r3) * 5
          p3 = a0 r3 + a1 r2 + a2 r1 + a3 r0          + (a4 r4) * 5
          p4 = a0 r4 + a1 r3 + a2 r2 + a3 r1 +  a4 r0

          >>
       *)

      Definition MULR : code progvar :=
        [
          p0   ::= a0 [*] r0;
          temp ::= a1 [*] r4; temp ::=* Five; p0 ::=+ temp;
          temp ::= a2 [*] r3; temp ::=* Five; p0 ::=+ temp;
          temp ::= a3 [*] r2; temp ::=* Five; p0 ::=+ temp;
          temp ::= a4 [*] r1; temp ::=* Five; p0 ::=+ temp;

          p1   ::= a0 [*] r1;
          temp ::= a1 [*] r0;
          temp ::= a2 [*] r4; temp ::=* Five; p1 ::=+ temp;
          temp ::= a3 [*] r3; temp ::=* Five; p1 ::=+ temp;
          temp ::= a4 [*] r2; temp ::=* Five; p1 ::=+ temp;


          p2   ::= a0 [*] r2;
          temp ::= a1 [*] r1; p2   ::=+ temp;
          temp ::= a2 [*] r0; p2   ::=+ temp;
          temp ::= a3 [*] r4; temp ::=* Five; p2 ::=+ temp;
          temp ::= a4 [*] r2; temp ::=* Five; p2 ::=+ temp;


          p3   ::= a0 [*] r3;
          temp ::= a1 [*] r2; p3   ::=+ temp;
          temp ::= a2 [*] r1; p3   ::=+ temp;
          temp ::= a3 [*] r0; p3   ::=+ temp;
          temp ::= a4 [*] r2; temp ::=* Five; p3 ::=+ temp;


          p4   ::= a0 [*] r4;
          temp ::= a1 [*] r3; p4 ::=+ temp;
          temp ::= a2 [*] r2; p4 ::=+ temp;
          temp ::= a3 [*] r1; p4 ::=+ temp;
          temp ::= a4 [*] r0; p4 ::=+ temp;
          ASSERT NVal (Val p0) (Val p1) (Val p2) (Val p3) (Val p4) =
                 NVal (Val a0) (Val a1) (Val a2) (Val a3) (Val a4) *
                 NVal (Val r0) (Val r1) (Val r2) (Val r3) (Val r4)
        ]%list%N.

  End Poly1305.
End Internal.


Definition loadClaim : Prop.
  exParamProp Internal.LOAD_COEFFICIENT.
Defined.

Definition locadCorrectness : loadClaim.
  unfold loadClaim. unfold genSAT. unfold SAT. breakStore.
  lazy -[RotR RotL ShiftR ShiftL XorW AndW OrW NegW
              fromNibbles
              numBinOp numUnaryOp numBigargExop numOverflowBinop
              Nat.add Nat.sub Nat.mul Nat.div Nat.pow
              N.add N.sub N.mul N.div N.div_eucl N.modulo
              N.pow
              Ox nth replace].
Abort.


Definition MulClaim : Prop.
  exParamProp Internal.MULR.
Defined.

Definition MulCorrectness : MulClaim.
  unfold MulClaim.
Abort.