Require Import Verse.
Require Import Verse.CryptoLib.blake2.
Require Import Nat.


(** * Blake2 implementation in C

This module provides the implementation of blake2 hashes in C. Both
blake2b and blake2s implementations can be recovered from this module
by passing the apporpriate config module [C : CONFIG].


*)

Module Blake2 (C : CONFIG).

  Import C.

  Definition Word : type direct  := word WORD_LOG_SIZE.
  Definition Hash  := Array HASH_SIZE  hostE Word.
  Definition Block := Array BLOCK_SIZE littleE Word.
  Definition IV i (pf : i < 8) := Vector.nth_order IVVec pf.

  (** Unlike the sha2 hashes, there is a difference in the structure
      of blake2 in that there are special steps to be taken for the
      last block. We leave out the padding issue for the last block
      and expect the calling function to take care of this. Even
      ignoring the padding, there are certain differences in the two.

      - As opposed to a Merkel-Damgard hash like sha512, every block
        needs the length of the message hashed sofar as its
        argument. In the initial blocks, the lengths get updated by
        the blocksize. However, the last block could be partial and
        hence including this length in the compression should be done
        carefully.

      - The last block also needs special finalisation flags. While,
        these flags can be fixed when blake2 is run as a cryptographic
        hash, the blake2 standard allows for other modes of operation
        like message authentication and tree hashing which uses
        different finalisation flags. Implementations here provide the
        flexibility for tweaking these.

      Due to the above reason, the module provides two functions, a
      _blake2 iterator_, or _iterator_ for short that handles data in
      multiples of blocks, and the _blake2 last block compressor_ or
      _compressor_ for short which handles the last block of the
      message.

      We follow the standard idiom where the code for the iterator and
      the last block compressor is wrapped into a section called
      [Program].  *)

  Section Program.

    (** ** Program variables.

      The program parameters and other variables become parameters to
      the section of type [VariableT]. The iterator and the last block
      compressor share a lot of program variables but there are indeed
      variables that are relevant to one but not the other. We define
      all these variables together in the same section. Since any coq
      definition inside a section only has parameters that are
      mentioned in the definiton, this works out well for use. The
      only difference is that we need to be have two sets of
      parameter, stack and register declaration in the code.

     *)

    Variable progvar : VariableT.
    Arguments progvar [k] _.

    (** *** Parameters.

      The difference in the parameter list comes due to the following
      reasons.

      - The iterator does not need to mention its message and the
        count as these are implicitly supplied during the code
        generation of an iterator, where as for the last block
        compressor needs to define these explicitly.

      - The iterator is not done with the message yet, so it has a
        responsibility to update the total count of bytes processed.
        On the other hand the last block compressor only needs the
        count of the bytes processed while compressing the last
        block. Since there are no more blocks of message, it need not
        update the count value. Due to the above difference, the
        count, kept track of using two words, is passed as a reference
        variable in iterator as opposed to normal variables in the
        last block compressor.

      - Finally the last block compressor needs finalisation constants
        that need to be passed around which clearly the iterator does
        not need


      To summarise we have the following

       - The reference variables [UpperRef], and [LowerRef] that is
         unique to to the iterator,

       - The variables [LastBlock], [NBytes], [Upper] [Lower], [f0]
         and [f1] unique to the last block iterator, and

       - The variable [hash] which is common to both.

     *)



    Variable UpperRef LowerRef : progvar (Ref Word).

    Variable LastBlock : progvar Block.
    Variable NBytes    : progvar Word.
    Variable Upper Lower : progvar Word.
    Variable f0 f1: progvar Word.

    Variable hash : progvar Hash.


    Definition paramIterator  : Declaration
      := [Var UpperRef; Var LowerRef; Var hash].
    Definition paramLastBlock : Declaration
      := [Var LastBlock; Var NBytes; Var Upper; Var Lower; Var f0; Var f1; Var hash].

    (** *** The stack variables.

        The iterator also keeps a copy of the hash in local variables
        to speed up access. On register rich machines this could
        potentially end up on actual registers and hence could become
        fast.

     *)
    Variable h0 h1 h2 h3 h4 h5 h6 h7 : progvar Word.
    Definition stack : Declaration := Vector.map Var [h0 ;h1 ;h2; h3; h4; h5; h6; h7].
    Definition H  : VarIndex progvar 8 Word := varIndex [h0; h1; h2; h3; h4; h5; h6; h7].

    (** *** The register variables.

        We start with a register cache for the message block.

     *)
    Variable w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : progvar Word.

    Definition message_variables
      := [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15].



    (** *** The state variables

        The state of the hashing function is a 4x4 matrix of
        words. The rounds transform this state using the [G] functions
        applied to either the rows or the diagonals of this matrix.

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

    (** *** Registers to manage byte count.

        Recall that each of the blake2 blocks is compressed using a
        compression function that makes use of the length of the
        message as auxiliary input. The message length is kept track
        of as a set of two words and hence we need to explicitly do
        arithmetic in twice the precision. In the iterator this byte
        count is kept in the reference variables [UpperRef] and
        [LowerRef] where as in the last block compressor it is merely
        passed as parameters [Upper] and [Lower]. As a result these
        functions have the following additional register variables.

        - The [C] and the [LMSB] registers used to perform the count
          update with twice the precision. The variable [C] is used to
          compute the carry generated when the lower words are added
          and the [LMSB] is used as an intermediate register to hold
          the most significant bit of the lower portion of the count.

        - The iterator also define two variables [U] and [V] that is
          to be used instead of the reference variables [UpperRef] and
          [LowerRef].


     *)

    Variable C LMSB : progvar Word.
    Variable U L    : progvar Word.

    Definition regLastBlock
      := Vector.map Var (Vector.append (Vector.append message_variables state) [C ; LMSB]).

    Definition regIterator : Declaration
      := Vector.append regLastBlock  (Vector.map Var [ U   ; L])%vector.


    (** ** Updating the count.

        The main idea is to compute the carry arising while adding the
        lower word.

        - Compute the carry occurring on most significant bit by
          masking off the MSB and performing the addition. Shift it to
          the least significant bit.

        - Compute the MSB of the lower word and shift it to the least
          significant bit.

        - Add the previous two carries to obtain the carry occurring
          on the MSB of the lower word in bit position 2.

        - Shift it right once more to obtain the actual carry.

     *)

    Section UpdateCount.

      Hint Resolve NPeano.Nat.add_pos_pos.
      Hint Resolve NPeano.Nat.add_pos_nonneg.
      Hint Constructors le.
      Lemma zeroLtPower2 : forall n, 0 < 2 ^ n.
        intros; induction n; simpl; eauto.
      Qed.
      Hint Resolve zeroLtPower2.

      (** This constant used to mask out the top most bit for
          computing the carry
       *)
      Definition mask : constant Word.
        refine (let allones := Vector.const OxF (2*2^WORD_LOG_SIZE) in
                @Vector.replace_order _ _ allones 0 _ Ox7); simpl.
        eauto.
      Defined.


      (* To make the update count work uniformly both for the iterator
         as well as the last block compressor, we need to parameterise
         over both the upper and lower arguments and also the size
         argument.
       *)

      Variable A : Type.
      Variable a_is_rarg : RARG progvar Word A.
      Variable byteCount : A.

      Definition UPDATE_COUNTER (u l : progvar Word) : code progvar :=
        [ (* We first ensure that the variable C gets the carry that overflows
             when l is added bsize. For this we first need to get the msb of l
             into the lsb position
           *)

          LMSB ::= l;
          LMSB ::=>> (8 * size(Word) - 1); (* get he msb to the lsb *)

          (* Now get the carry that flows into MSB from the previous bits *)
          C  ::= l & mask; (* select every bit except msb *)
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

    (** The update count function as defined for the iterator and the
        last block compressor respectively *)
    Definition UPDATE_COUNTER_ITER :=
      let bsize : constant Word := fromNat (BLOCK_SIZE * size Word)
      in UPDATE_COUNTER bsize U L.

    Definition UPDATE_COUNTER_LAST := UPDATE_COUNTER NBytes Upper Lower.

    (** ** The blake round function.


      A single round of blake function consists of performing the G
      function, first on the rows and then on the diagonals of the
      state matrix. The message words that are used change merely
      permuted and then used respectively.

     *)

    (** *** The G function.

        The G function defined below takes 4 words which constitute
        either a row or a diagonal of the state matrix. In addition it
        takes two message words

     *)

    Definition G (a b c d m0 m1 : progvar Word) : code progvar :=
      [
        a ::=+ b; a ::=+ m0; d ::=^ a; d ::=>>> R0;
        c ::=+ d;            b ::=^ c; b ::=>>> R1;
        a ::=+ b; a ::=+ m1; d ::=^ a; d ::=>>> R2;
        c ::=+ d;            b ::=^ c; b ::=>>> R3
      ]%list.

    (** *** Message permutations.

       Each round uses the entire set of the message word but
       in different order captured by a message permutations

     *)

    Definition Perm := Vector.t {i | i < BLOCK_SIZE} BLOCK_SIZE.
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

    (** Let us digress a bit and prove that the above shuffles are
        indeed permutations.  *)
    Tactic Notation "crush_forall" tactic(tac)
      := repeat match goal with
                | [ |- Vector.Forall _  _  ] => constructor
                | _ => tac
                end.

    Theorem round_perms_are_permutations :  Vector.Forall (@Permutation BLOCK_SIZE) RoundPerms .
      crush_forall (compute; crush_permutation_obligation 16).
    Qed.

    (** *** The round function.

         We now give the blake round function as a section
         parameterised by the round number.

     *)

    Section Round.

      Variable r : nat.
      Variable rBondPf : r < ROUNDS.

      (** The register cache corresponding to the permuted message *)
      Definition M : VarIndex progvar BLOCK_SIZE Word.
        verse (varIndex (select message_variables
                                (@Vector.nth_order _ _ RoundPerms (r mod 10) _))).
      Defined.

      Definition ROUND : code progvar.
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

    (** The entire set of rounds *)
    Definition ALL_ROUNDS := iterate ROUND.


    Definition SETUP : code progvar.
      verse ( [ U ::= UpperRef[- 0 -]; L ::= LowerRef[- 0 -] ] ++ loadCache hash H ).
    Defined.

    (** ** The initialisation of state.

        The initialisation uses the previous hash values and the
        iv. Depending on whether the initialisation for a block in
        between or the last block there is a slight difference in the
        initialisation code.

     *)
    Definition INIT_STATE : code progvar.
      verse
        [ v0 ::= h0;
	  v1 ::= h1;
	  v2 ::= h2;
	  v3 ::= h3;
	  v4 ::= h4;
	  v5 ::= h5;
	  v6 ::= h6;
	  v7 ::= h7;
	  v8  ::= IV 0 _;
	  v9  ::= IV 1 _;
	  v10 ::= IV 2 _;
	  v11 ::= IV 3 _;
	  v12 ::= IV 4 _ ^ L;
	  v13 ::= IV 5 _ ^ U;
	  v14 ::= IV 6 _ ;
	  v15 ::= IV 7 _
        ]%list.
    Defined.

    Definition INIT_STATE_LAST : code progvar.
      verse
        [ v0 ::= h0;
	  v1 ::= h1;
	  v2 ::= h2;
	  v3 ::= h3;
	  v4 ::= h4;
	  v5 ::= h5;
	  v6 ::= h6;
	  v7 ::= h7;
	  v8  ::= IV 0 _;
	  v9  ::= IV 1 _;
	  v10 ::= IV 2 _;
	  v11 ::= IV 3 _;
	  v12 ::= IV 4 _ ^ Lower;
	  v13 ::= IV 5 _ ^ Upper;
	  v14 ::= IV 6 _ ^ f0;
	  v15 ::= IV 7 _ ^ f1
        ]%list.
      Defined.


    (** ** Load message into register cache.

        To speed up the hashing we load the message into the register
        cache W.

     *)
    Definition W : VarIndex progvar BLOCK_SIZE Word := varIndex message_variables.
    Definition LOAD_MESSAGE_I (blk : progvar Block) (i : nat) (pf : i < BLOCK_SIZE)
      : code progvar.
      verse [ W i _ ::= blk [- i -] ]%list.
    Defined.
    Definition LOAD_MESSAGE (blk : progvar Block)
      := foreach (indices blk) (LOAD_MESSAGE_I blk).


    (** ** Updating the hash.

        After performing the rounds of blake, the hash gets updated as follows.

     *)
    Definition UPDATE_HASH : code progvar :=
      [ h0 ::=^ v0 ; h0 ::=^ v8;
        h1 ::=^ v1 ; h1 ::=^ v9;
        h2 ::=^ v2 ; h2 ::=^ v10;
        h3 ::=^ v3 ; h3 ::=^ v11;
        h4 ::=^ v4 ; h4 ::=^ v12;
        h5 ::=^ v5 ; h5 ::=^ v13;
        h6 ::=^ v6 ; h6 ::=^ v14;
        h7 ::=^ v7 ; h7 ::=^ v15
      ]%list.

    (** In the iterator one needs to update the hash array as well as
        the reference variables UpperRef and LowerRef.  *)
    Definition FINALISE : code progvar.
      verse ([ MOVE U TO UpperRef[- 0 -]; MOVE L TO LowerRef[- 0 -] ] ++ moveBackCache hash H ).
    Defined.


    Definition PROCESS_BLOCK blk :=
      LOAD_MESSAGE blk
      ++ ALL_ROUNDS
      ++ UPDATE_HASH.

    (** ** The BLAKE2 iterator and the last block compressor.  *)
    Definition Iterator : iterator Block progvar :=
      {| setup   := SETUP;
         process := fun blk => UPDATE_COUNTER_ITER ++ INIT_STATE ++ PROCESS_BLOCK blk;
         finalise := FINALISE
      |}.

    Definition LastBlockCompress :=
      loadCache hash H
                ++ UPDATE_COUNTER_LAST
                ++ INIT_STATE_LAST
                ++ PROCESS_BLOCK  LastBlock
                ++ moveBackCache hash H.
    End Program.

End Blake2.
