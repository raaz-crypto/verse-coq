Require Import Verse.
Require Import Verse.CryptoLib.sha2.
Import Nat.
Require Vector.
Import VectorNotations.
Delimit Scope vector_scope with vector.
Require Import List.
Import ListNotations.

Module Type SIGMA (C : CONFIG).

  (** * Sigma functions.

A single step in the evaluation of Sha256 or Sha512 uses the sigma
functions. Since we need to generate code that evaluate these sigma
functions we parameterise them by verse code that take two program
variables [temp] and [x] and generates code that will compute sigma(x)
in [temp].

   *)

  Parameter SIGB0 : forall v : VariableT, v direct C.Word -> v direct C.Word -> code v.
  Parameter SIGB1 : forall v : VariableT, v direct C.Word -> v direct C.Word -> code v.

  Parameter SIGS0 : forall v : VariableT, v direct C.Word -> v direct C.Word -> v direct C.Word -> code v.
  Parameter SIGS1 : forall v : VariableT, v direct C.Word -> v direct C.Word -> v direct C.Word -> code v.

End SIGMA.

(*

#define SIGS1(x)     (RotateR(x,17) ^ RotateR(x,19) ^ ShiftR(x,10))

*)

(* Helper functions that does cyclic shifts. *)

Definition rotateLeft {A}{n} (vec : Vector.t A (S n)) : Vector.t A (S n) :=
  match vec with
  | (m0 :: rest)%vector => Vector.shiftin m0 rest
  end.

Definition rotateRight {A}{n} (vec : Vector.t A (S n)) : Vector.t A (S n) :=
  let x    := Vector.last vec in
  let vecp := Vector.shiftout vec in
  (x :: vecp)%vector.


Module SHA2 (C : CONFIG)(CO : SIGMA C).
  (** We parameterise this section over the word type used. Sha256
      uses Word32 where as SHA512 uses Word64 *)

  Import C.
  Import CO.
  Definition Hash  := Array HASH_SIZE  hostE Word.
  Definition Block := Array BLOCK_SIZE bigE Word.


  (** We start with defining some helper function that is used in the rounds

   *)


  Section Program.

    Variable v : VariableT.
    Arguments v [k] _.


    (** The message schedule as a set of variables. We only need to
        keep track of a window of [BLOCK_SIZE] many [Word] at any
        given point of time

     *)

    Section Helpers.

      Variable t tp : v Word.

      (* Computers the expression [(x & y) ^ (not x & z)] into [t]
         using [tp] as a temp variable.  *)

      Definition CH (x y z : v Word) : code v := [ tp ::=~ x; tp ::=& z; t ::= x [&] y; t ::=^ tp ].

      Definition MAJ (x y z : v Word) : code v := [ t ::= y [|] z; t ::=& x; tp ::= y [&] z; t ::=| tp ].

    End Helpers.


    (** * The main iterator for SHA2

        We are now ready define the main iterator for the SHA2 hash.

     *)

    Section SHA2Iterator.



    (** ** Program variables.

        We begin by defining the program variables. Recall that, the
        standard idiom of verse is to declare the parameters, local
        variables, and register variables in that order.

     *)

    (** *** Parameters

        SHA2 hashes are Merkel-Damgrad hash. Hence it needs only the
        hash of the previous blocks to process the current block. Thus
        there is only one parameter for the hash function namely the
        hash of the previous block.

     *)

    Variable hash : v Hash.

    Definition parameters : Declaration := [ Var hash ].

    (** *** Local variables.

        We keep the current block in a set of local variables. The
        advantage of this is that on a register rich machine all of
        them could be allocated in registers and thus could be faster.

     *)

    Variable w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : v Word.

    Definition message_variables := [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]%vector.

    Definition locals : Declaration := List.map Var (Vector.to_list message_variables).




    (** ** The state and temporary variables

     We choose to put them in registers as there are the variables
     that are frequently used.

     *)


    Variable a b c d e f g h : v Word.
    Variable t tp temp       : v Word.

    Definition state_variables := [ a ; b ; c ; d ; e ; f ; g ; h ]%vector.

    Definition registers : Declaration := List.map Var (Vector.to_list state_variables ++ [ t ; tp ; temp]).




  (** * The hash transformation

  The hashing algorithm transforms a state consisting of [HASH_SIZE]
  many [Word]s into in [ROUNDS] many rounds. Each round uses a message
  word that is scheduled for that particular round. This section
  builds code towards implementing these.

   *)




    Definition W : VarIndex v BLOCK_SIZE Word := varIndex message_variables.
    Definition LOAD_BLOCK (blk : v Block) := loadCache blk W.




   (* ** Message scheduling

Although the message scheduling requires [ROUNDS+1] many values, we
only need to keep track of a window of 16 values. Therefore the
message scheduling can be obtained by updating the current message
using the expression [ m += S0 mm15 + mm7 + S1 mm2 ]
   *)


    Definition M (r : nat) : v Word.
      verse (W (r mod BLOCK_SIZE) _).
    Defined.

    Definition SCHEDULE (r : nat): code v :=
      let m16 := M r in
      let mm i := M (r + 16 - i) in
      SIGS0 v t tp (mm 15)
            ++ [ m16 ::=+ t; m16 ::=+ mm 7 ]
            ++ SIGS1 v t tp (mm 2)
            ++ [m16 ::=+ t ].



    (** ** Individual rounds.

    The state of the hash function is kept track of in the set of
    variables a-h, and in the rth round the update is given by

     *)



    (**

<< a' = t1 + t2

b' = a

c' = b

d' = c

e' = d + t1

f' = e

g' = f

h' = g

>>

where

<<

t1 = h + k + m + SIGB1 e + CH e f g

t2 = SIGB0 a + MAJ a b c

>>


     *)

(** So in each round we compute the following

<<

temp = h + k + m + σ₁(e) + CH(e,f,g)

d += temp;

h = temp + σ₀(a) + MAJ(a,b,c); >>

 *)

    Definition ST : VarIndex v HASH_SIZE Word := varIndex state_variables.
    Definition LOAD_STATE : code v := loadCache hash ST.



    Definition STATE (r : nat) (i : nat) : v Word.
      verse(
          let rp  := r mod HASH_SIZE in
          let idx := i + (16 - rp) in
          ST (idx mod HASH_SIZE) _).
      Show Proof.
    Defined.

    Definition K (r : nat)(pf : r < ROUNDS) : constant Word :=  Vector.nth_order KVec pf.

    Definition STEP (r : nat) (pf : r < ROUNDS) : code v.
      verse (
          let A := STATE r 0 in
          let B := STATE r 1 in
          let C := STATE r 2 in
          let D := STATE r 3 in
          let E := STATE r 4 in
          let F := STATE r 5 in
          let G := STATE r 6 in
          let H := STATE r 7 in
          let RK : constant Word := K r pf in
          [ temp ::= H [+] RK ; temp ::=+ M r ] (* temp = h + K + M *)
            ++ CH t tp E F G                 (* t = CH e f g *)
            ++ [ temp ::=+ t ]               (* temp = h + K + M + CH e f g *)
            ++ SIGB1 v t E                   (* t = σ₁(e) *)
            ++ [ temp ::=+ t;                (* temp = σ₁(e) + h + K + M + CH e f g *)
                 D ::=+ temp
               ]
            ++ MAJ t tp A B C
            ++ [ temp ::=+ t ]       (* temp = σ₁(e) + h + K + M + CH e f g  + MAJ a b c*)
            ++ SIGB0 v t A
            ++ [ H ::= temp [+] t ]  (* h = σ₁(e) + h + K + M + CH e f g  + MAJ a b c + σ₀(e) *)
        ).
      Defined.

    Definition UPDATE_ITH (i : nat) (pf : i < HASH_SIZE) : code v.
      verse ([ST i _ ::=+ hash [- i -]]).
    Defined.

    Definition UPDATE : code v
      := foreach (indices hash) UPDATE_ITH ++ moveBackCache hash ST.


    Definition Round (r : nat)(rp : r < ROUNDS) : code v :=
      if leb r (ROUNDS - BLOCK_SIZE - 1) then STEP r rp ++ SCHEDULE r else STEP r rp .

    Definition ALL_ROUNDS : code v := iterate Round.
    Definition sha2 : iterator Block v :=
      {|
        setup   := LOAD_STATE;
        process := fun block => (LOAD_BLOCK block
                                         ++ ALL_ROUNDS
                                         ++ UPDATE);
        finalise := []
      |}.

    End SHA2Iterator.
  End Program.

End SHA2.
