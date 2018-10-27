Require Import Verse.
Require Import Verse.CryptoLib.blake2.
Require Import List.
Import ListNotations.

Require Vector.
Require Import Nat.
Import VectorNotations.


(**

The blake2 implementation exposes both an iterator and a last block
compressor. The iterator compresses in multiple of blocks and the last
block compressor only handles the last < blocksize bytes. The last
bock compressor assumes the following

1. The buffer is of size at least the block length and

2. Appropriate message padding has already been done and thus does not
   bother to pad the date.

*)

Module Blake2 (C : CONFIG).

  Import C.

  Definition Word : type direct  := word WORD_LOG_SIZE.
  Definition Hash  := Array HASH_SIZE  hostE Word.
  Definition Block := Array BLOCK_SIZE littleE Word.


  (**
      Type that captures a permutation of the message values. We
      represent permutations by giving the vector of indices.
   *)
  Definition Perm := Vector.t {i | i < BLOCK_SIZE} BLOCK_SIZE.

    (** The round permutations of blake. Beyond round 10 it repeats the cycle. *)

    Definition RoundPerms : Vector.t Perm 10
      := [
          shuffleIndices [0 ;  1;  2;  3;  4;  5;  6;  7;  8;  9; 10; 11; 12; 13; 14; 15];
	  shuffleIndices [14; 10;  4;  8;  9; 15; 13;  6;  1; 12;  0;  2; 11;  7;  5;  3];
	  shuffleIndices [11;  8; 12;  0;  5;  2; 15; 13; 10; 14;  3;  6;  7;  1;  9;  4];
	  shuffleIndices [7 ;  9;  3;  1; 13; 12; 11; 14;  2;  6;  5; 10;  4;  0; 15;  8];
	  shuffleIndices [9 ;  0;  5;  7;  2;  4; 10; 15; 14;  1; 11; 12;  6;  8;  3; 13];
	  shuffleIndices [2 ; 12;  6; 10;  0; 11;  8;  3;  4; 13;  7;  5; 15; 14;  1;  9];
	  shuffleIndices [12;  5;  1; 15; 14; 13;  4; 10;  0;  7;  6;  3;  9;  2;  8; 11];
	  shuffleIndices [13; 11;  7; 14; 12;  1;  3;  9;  5;  0; 15;  4;  8;  6;  2; 10];
	  shuffleIndices [6 ; 15; 14;  9; 11;  3;  0;  8; 12;  2; 13;  7;  1;  4; 10;  5];
	  shuffleIndices [10;  2;  8;  4;  7;  6;  1;  5; 15; 11;  9; 14;  3; 12; 13;  0]
        ]%vector.

    Tactic Notation "crush_forall" tactic(tac)
      := repeat match goal with
                | [ |- Vector.Forall _  _  ] => constructor
                | _ => tac
                end.

    (** Let us prove that the round permutations are indeed permutations. *)

    Theorem round_perms_are_permutations :  Vector.Forall (@Permutation BLOCK_SIZE) RoundPerms .
      crush_forall (compute; crush_permutation_obligation 16).
    Qed.

    (** The blake2 implementation exposes both an iterator and a last
        block compressor. The iterator compresses in multiple of
        blocks and the last block compressor only handles the last <
        blocksize bytes. The last bock compressor assumes the
        following.

        * The buffer is of size at least the block length, and

        * Appropriate message padding has already been done and thus
          does not bother to pad the date.

        We follow the standard idiom for defining these two
        functions. The two function has a slightly different set of
        parameters and local register set. We use a single section for
        both but distinguish there parameter and register list.

     *)

    Section Program.

      Variable progvar : VariableT.
      Arguments progvar [k] _.

      (** The G function. Takes 4 words which is either a row or
          diagonal of the state and two message words. *)

      Definition G (a b c d m0 m1 : progvar Word) : code progvar :=
        [ a ::=+ b; a ::=+ m0; d ::=^ a; d ::=>*> R0;
          c ::=+ d;            b ::=^ c; b ::=>*> R1;
          a ::=+ b; a ::=+ m1; d ::=^ a; d ::=>*> R2;
          c ::=+ d;            b ::=^ c; b ::=>*> R3
        ]%list.

      (** * Parameters.


        The arguments taken by the function are the total bytes hashed
        sofar and the hash sofar. The count of the data is kept in two
        words. The iterator needs to update these count and hence
        takes the arguments as reference variables whereas the last
        block compressor takes.

       *)

      (** The array containing the last block. This is a parameter
          only for the last block compressor as the iterator gets it
          blocks implicitly.
       *)

      Variable LastBlock : progvar Block.
      Variable NBytes    : progvar Word.

      (** The reference variables that keeps track of the count of
          bytes hashed. These counts are updated by the iterator and hence
          needs to be reference variables
       *)
      Variable UpperRef LowerRef : progvar (Ref Word).

      (** On the other hand the last block compressor does not need to
          update any more as all uses of the count is already done. So
          the variant here are ordinary variables.  *)
      Variable Upper Lower : progvar Word.

      (** The finalisation flags. These are only relevant for the last block *)
      Variable f0 f1: progvar Word.
      (** Finally the variable that contains the hash that is computed
      so far. Both the iterator and the last block compressor needs
      this parameter *)
      Variable hash : progvar Hash.


      Definition paramIterator  : Declaration
        := [Var UpperRef; Var LowerRef; Var hash].
      Definition paramLastBlock : Declaration
        := [Var LastBlock; Var NBytes; Var Upper; Var Lower; Var f0; Var f1; Var hash].

      Variable h0 h1 h2 h3 h4 h5 h6 h7 : progvar Word.
      Definition H  : VarIndex progvar 8 Word := varIndex [h0; h1; h2; h3; h4; h5; h6; h7].
      Definition stack : Declaration := Vector.map Var [h0 ;h1 ;h2; h3; h4; h5; h6; h7].

      (** Register cache for the current block *)
      Variable w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : progvar Word.

      Definition message_variables
      := [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15].

      Definition W : VarIndex progvar BLOCK_SIZE Word := varIndex message_variables.


    (** * The state variables

        The state of the hashing function is a 4x4 matrix of
        words. The rounds transform this state using the [G] function.

     *)
    Variable v0 v4 v8  v12
             v1 v5 v9  v13
             v2 v6 v10 v14
             v3 v7 v11 v15 : progvar Word.

    Definition state := [ v0 ; v4 ; v8  ; v12;
                          v1 ; v5 ; v9  ; v13;
                          v2 ; v6 ; v10 ; v14;
                          v3 ; v7 ; v11 ; v15
                        ].

    (** The iterator needs registers U, L which together keep track of
       the total bytes hashed so far. In the case of the last block iterator, we reuse
       the parameters Upper and Lower and do not need them
     *)

    Variable U L    : progvar Word.

    (** While updating the count, we need to keep track of the carry
        from the lower word to the higher word and these variables are
        used for that purpose. They are required by both the iterator
        and their last block compressor *)

    Variable C LMSB : progvar Word.

    Definition commonRegs := Vector.append message_variables state.
    Definition regIterator : Declaration
      := Vector.map Var (Vector.append commonRegs [ U   ; L   ; C ; LMSB])%vector.
    Definition regLastBlock : Declaration :=
      Vector.map Var (Vector.append commonRegs [ C ; LMSB]).

    (** Code to update the count of bytes *)
    Section UpdateCount.

      Hint Resolve NPeano.Nat.add_pos_pos.
      Hint Resolve NPeano.Nat.add_pos_nonneg.
      Hint Constructors le.
      Lemma zeroLtPower2 : forall n, 0 < 2 ^ n.
        intros; induction n; simpl; eauto.
      Qed.
      Hint Resolve zeroLtPower2.

      (** This mask is used to mask out the top most bit for computing the carry *)
      Definition mask : constant Word.
        refine (let allones := Vector.const xF (2*2^WORD_LOG_SIZE) in
                @Vector.replace_order _ _ allones 0 _ x7); simpl.
        eauto.
      Defined.
      (** Block size now as a program constant *)
      Definition bsize : constant Word := fromNat (BLOCK_SIZE * size Word).

      Variable A : Type.
      Variable a_is_rarg : RARG progvar direct Word A.
      Variable byteCount : A.
      Definition UPDATE_COUNTER (u l : progvar Word) : code progvar :=
        [ (* We first ensure that the variable C gets the carry that overflows
             when l is added bsize. For this we first need to get the msb of l
             into the lsb position
           *)

          LMSB ::== l;
          LMSB ::=>> (8 * size(Word) - 1); (* get he msb to the lsb *)

          (* Now get the carry that flows into MSB from the previous bits *)
          C  ::= l [&] mask; (* select every bit except msb *)
          C  ::=+ byteCount; (* carry at the msb position   *)
          C  ::=>> (8 * size(Word) - 1); (* move it to the lsb *)

          C  ::=+ LMSB; (* the second now has the carry of the addition    *)
          C  ::=>> 1;   (* move it to the lsb so that it can be added to u *)

          (* increment the u:l byte count. u gets added the carry and
             l the bsize
           *)
          u  ::=+ C;
          l  ::=+ byteCount
        ]%list.
    End UpdateCount.

    Arguments UPDATE_COUNTER [A a_is_rarg] _ _ _ .
    Definition UPDATE := UPDATE_COUNTER bsize U L.
    Definition UPDATE_LAST := UPDATE_COUNTER NBytes U L.

    Section Round.
      Variable r : nat. (** Round number *)
      Variable rBondPf : r < ROUNDS.

      Print Vector.nth_order.
      Definition M : VarIndex progvar BLOCK_SIZE Word.
        verse( varIndex (select message_variables
                                (@Vector.nth_order _ _ RoundPerms (r mod 10) _))).
      Defined.

      Definition round : code progvar.
        verse (G v0 v4 v8  v12 (M 0 _) (M 1 _) ++
               G v1 v5 v9  v13 (M 2 _) (M 3 _) ++
               G v2 v6 v10 v14 (M 4 _) (M 5 _) ++
               G v3 v7 v11 v15 (M 6 _) (M 7 _) ++

               G v0 v5 v10 v15 (M 8 _)  (M 9  _) ++
               G v1 v6 v11 v12 (M 10 _) (M 11 _) ++
               G v2 v7 v8  v13 (M 12 _) (M 13 _) ++
               G v3 v4 v9  v14 (M 14 _) (M 15 _)).
      Defined.
    End Round.

    Definition ALL_ROUNDS := iterate round.

    (** We are now ready to define both the iterator and the last block compressor *)

    Definition SETUP : code progvar.
      verse ( [ U ::== UpperRef[- 0 -]; L ::== LowerRef[- 0 -] ] ++ loadCache hash H ).
    Defined.

    Definition IV i (pf : i < 8) := Vector.nth_order IVVec pf.

    Definition INIT_STATE : code progvar.
      verse
        [ v0 ::== h0;
	  v1 ::== h1;
	  v2 ::== h2;
	  v3 ::== h3;
	  v4 ::== h4;
	  v5 ::== h5;
	  v6 ::== h6;
	  v7 ::== h7;
	  v8  ::== IV 0 _;
	  v9  ::== IV 1 _;
	  v10 ::== IV 2 _;
	  v11 ::== IV 3 _;
	  v12 ::= IV 4 _ [^] L;
	  v13 ::= IV 5 _ [^] U;
	  v14 ::== IV 6 _ ;
	  v15 ::== IV 7 _
        ]%list.
    Defined.


    Definition INIT_STATE_LAST : code progvar.
      verse
        [ v0 ::== h0;
	  v1 ::== h1;
	  v2 ::== h2;
	  v3 ::== h3;
	  v4 ::== h4;
	  v5 ::== h5;
	  v6 ::== h6;
	  v7 ::== h7;
	  v8  ::== IV 0 _;
	  v9  ::== IV 1 _;
	  v10 ::== IV 2 _;
	  v11 ::== IV 3 _;
	  v12 ::= IV 4 _ [^] L;
	  v13 ::= IV 5 _ [^] U;
	  v14 ::= IV 6 _ [^] f0;
	  v15 ::= IV 7 _ [^] f1
        ]%list.
      Defined.


    Definition LOAD_MESSAGE_I (blk : progvar Block) (i : nat) (pf : i < BLOCK_SIZE)
      : code progvar.
      verse [ W i _ ::== blk [- i -] ]%list.
    Defined.
    Definition LOAD_MESSAGE (blk : progvar Block)
      := foreach (indices blk) (LOAD_MESSAGE_I blk).


    Definition UPDATE_HASH : code progvar :=
      [ h0 ::=^ v0 ; h0 ::=^ v8;
        h1 ::=^ v1 ; h0 ::=^ v9;
        h2 ::=^ v2 ; h0 ::=^ v10;
        h3 ::=^ v3 ; h0 ::=^ v11;
        h4 ::=^ v4 ; h0 ::=^ v12;
        h5 ::=^ v5 ; h0 ::=^ v13;
        h6 ::=^ v6 ; h0 ::=^ v14;
        h7 ::=^ v7 ; h0 ::=^ v15
      ]%list.

    Definition FINALISE : code progvar.
      verse ([ MOVE U TO UpperRef[- 0 -]; MOVE L TO LowerRef[- 0 -] ] ++ moveBackCache hash H ).
    Defined.

    Definition Iterator : iterator Block progvar :=
      {| setup := SETUP;
         process := fun blk => UPDATE
                              ++ INIT_STATE
                              ++ LOAD_MESSAGE blk
                              ++ ALL_ROUNDS
                              ++ UPDATE_HASH;

         finalise := FINALISE
      |}.

    Definition LastBlockCompress :=
      loadCache hash H
                ++ UPDATE_LAST
                ++ INIT_STATE
                ++ LOAD_MESSAGE LastBlock
                ++ ALL_ROUNDS
                ++ moveBackCache hash H.


  End  Program.
End Blake2.
