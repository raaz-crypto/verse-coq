Require Import Verse.
Require Import Verse.CryptoLib.sha2.
Import Nat.
Require Vector.
Import VectorNotations.
Delimit Scope vector_scope with vector.
Require Import List.
Import ListNotations.

Module Type SIGCODE (C : CONFIG).

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

End SIGCODE.

Module SIG256 : SIGCODE (SHA256Config).
  Section SIGS.
    Variable v  : VariableT.
    Variable t  : v direct Word32.
    Variable tp : v direct Word32.
    Variable x  : v direct Word32.

    (* sigb0(x) = RotateR(x,2) ^ RotateR(x,13) ^ RotateR(x,22) *)


    Definition SIGB0 : code v := [ t ::=  x >*> 9;
                                   t ::=^ x;    (* t = x +  x >>> 9 *)
                                   t ::=>*> 11; (* t = x >>> 11 + x >>> 20 *)
                                   t ::=^ x;    (* t = x + x>>>11 + x>>>20 *)
                                   t ::=>*> 2   (* t = x >>> 2 + x >>> 13 + x >>> 22 *)
                                 ].
    (* define sigb1(x) = RotateR(x,6) ^ RotateR(x,11) ^ RotateR(x,25) *)

    Definition SIGB1 : code v := [ t ::= x >*> 14;
                                   t ::=^ x;    (* t = x +  x >>> 14 *)
                                   t ::=>*> 5;  (* t = x >>> 5 + x >>> 19 *)
                                   t ::=^ x;    (* t = x + x>>>5 + x>>>19 *)
                                   t ::=>*> 6   (* t = x >>> 6 + x >>> 11 + x >>> 25 *)

                                 ].

    (* sigs0(x)     (RotateR(x,7) ^ RotateR(x,18) ^ ShiftR(x,3)  *)
    (* sigs1(x)     (RotateR(x,17) ^ RotateR(x,19) ^ ShiftR(x,10)  *)
    Definition SIGS0 : code v := [ tp ::=  x >> 3;
                                   t  ::=  x >*> 11;
                                   t  ::=^ x;        (* t = x ^ x >>> 11                *)
                                   t  ::=>*> 7;      (* t = x >>> 7 ^ x >>> 18          *)
                                   t  ::=^ tp        (* t = x >>> 7 ^ x >>> 18 ^ x >> 3 *)
                                 ].
    Definition SIGS1 : code v := [ tp ::=  x >> 10;
                                   t  ::=  x >*> 2;
                                   t  ::=^ x;        (* t = x ^ x >>> 2                *)
                                   t  ::=>*> 17;      (* t = x >>> 17 ^ x >>> 19       *)
                                   t  ::=^ tp        (* t = x >>> 17 ^ x >>> 19 ^ x >> 10 *)
                                 ].

    End SIGS.

End SIG256.
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


Module SHA2 (C : CONFIG)(CO : SIGCODE C).
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


    (** The round constants as a vector *)
    Definition CONSTANTS := Vector.t (constant Word) (S ROUNDS).

    (** The hash state as a vector of variables.  *)
    Definition STATE     := Vector.t (v Word) HASH_SIZE.

    (** The message schedule as a set of variables. We only need to
        keep track of a window of [BLOCK_SIZE] many [Word] at any
        given point of time

     *)

    Definition MESG := Vector.t (v Word) BLOCK_SIZE.


    Definition INTERNALS : Type :=  CONSTANTS * STATE * MESG.

    Definition next (i : INTERNALS) :=
      match i with
      | (c,s,m) => (rotateLeft c, rotateRight s, rotateLeft m)
      end.

    Section Helpers.

      Variable t tp : v Word.

      (* Computers the expression [(x & y) ^ (not x & z)] into [t]
         using [tp] as a temp variable.  *)

      Definition CH (x y z : v Word) : code v := [ tp ::=~ x; tp ::=& z; t ::= x [&] y; t ::=^ tp ].

      Definition MAJ (x y z : v Word) : code v := [ t ::= y [|] z; t ::=& x; tp ::= y [&] z; t ::=| tp ].

    End Helpers.

  (** * The hash transformation

  The hashing algorithm transforms a state consisting of [HASH_SIZE]
  many [Word]s into in [ROUNDS] many rounds. Each round uses a message
  word that is scheduled for that particular round. This section
  builds code towards implementing these.

   *)



    Section HashTransformation.

      (** Some temporary variables use in the message scheduling *)

      Variable t tp temp : v Word.

      Variable KV : CONSTANTS.
      Variable SV : STATE.
      Variable MV : MESG.



   (* ** Message scheduling

Although the message scheduling requires [ROUNDS+1] many values, we
only need to keep track of a window of 16 values. Therefore the
message scheduling can be obtained by updating the current message
using the expression [ m += S0 mm15 + mm7 + S1 mm2 ]
   *)


      Definition m (i : nat) : v Word.
        verse (@Vector.nth_order _ _ MV (i mod BLOCK_SIZE) _).
      Defined.

      Definition mm (r : nat) : v Word := m (16 - r).


      (** The SCHEDULE code fragment just does this update. *)

      Definition SCHEDULE : code v :=
        let m16 := Vector.hd MV in
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


      Definition s (i : nat) : v Word.
        verse (@Vector.nth_order _ _ SV (i mod HASH_SIZE) _).
      Defined.

      Definition STEP : code v :=
        let a := s 0 in
        let b := s 1 in
        let c := s 2 in
        let d := s 3 in
        let e := s 4 in
        let f := s 5 in
        let g  := s 6 in
        let h := s 7 in
        let K := Vector.hd KV in
        let M := Vector.hd MV in
        [ temp ::= h [+] K ; temp ::=+ M ] (* temp = h + K + M *)
          ++ CH t tp e f g                 (* t = CH e f g *)
          ++ [ temp ::=+ t ]               (* temp = h + K + M + CH e f g *)
          ++ SIGB1 v t e                   (* t = σ₁(e) *)
          ++ [ temp ::=+ t;                (* temp = σ₁(e) + h + K + M + CH e f g *)
               d ::=+ temp
             ]
          ++ MAJ t tp a b c
          ++ [ temp ::=+ t ]       (* temp = σ₁(e) + h + K + M + CH e f g  + MAJ a b c*)
          ++ SIGB0 v t a
          ++ [ h ::= temp [+] t ].  (* h = σ₁(e) + h + K + M + CH e f g  + MAJ a b c + σ₀(e) *)



    End HashTransformation.

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

    Definition W : VarIndex v BLOCK_SIZE Word := varIndex message_variables.


    (** ** The state and temporary variables

     We choose to put them in registers as there are the variables
     that are frequently used.

     *)

    Variable a b c d e f g h : v Word.
    Variable t tp temp       : v Word.

    Definition state_variables := [ a ; b ; c ; d ; e ; f ; g ; h ]%vector.

    Definition registers : Declaration := List.map Var (Vector.to_list state_variables ++ [ t ; tp ]).

    Definition ST : VarIndex v HASH_SIZE Word := varIndex state_variables.

    Definition LOAD_BLOCK (blk : v Block) := loadCache blk W.
    Definition LOAD_STATE : code v := loadCache hash ST.

    Definition UPDATE_ITH (i : nat) (pf : i < HASH_SIZE) : code v.
      verse [hash [- i -] ::=+ ST i _].
    Defined.

    Definition UPDATE : code v := foreach (indices hash) UPDATE_ITH.


    Fixpoint ALL_ROUNDS (n : nat) (internal : INTERNALS) : code v :=
      match n, internal with
      | S np, (k,s,m) => STEP t tp temp k s m ++ SCHEDULE t tp m ++ ALL_ROUNDS np (next internal)
      | _ , _         => []
      end.

    Definition start_internals : INTERNALS := (KVec,state_variables,message_variables).
    Definition sha2 : iterator Block v :=
      {|
        setup   := [];
        process := fun block => (LOAD_BLOCK block
                                        ++ LOAD_STATE
                                        ++ ALL_ROUNDS (S ROUNDS) start_internals
                                        ++ UPDATE);
        finalise := []
      |}.

    End SHA2Iterator.
  End Program.

End SHA2.
