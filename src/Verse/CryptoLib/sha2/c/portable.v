(** printing sigma  %$\sigma$%   #σ#  *)
(** printing sigma0 %$\sigma_0$% #σ<sub>0</sub># *)
(** printing sigma1 %$\sigma_1$% #σ<sub>1</sub># *)

(** printing Sigma  %$\Sigma$%   #Σ#  *)
(** printing Sigma0 %$\Sigma_0$% #Σ<sub>0</sub># *)
(** printing Sigma1 %$\Sigma_1$% #Σ<sub>1</sub># *)

(** printing mm7  %$m_{-7}$%     #m<sub>-7</sub>#  *)
(** printing mm15 %$m_{-15}$%    #m<sub>-15</sub># *)
(** printing mm2  %$m_{-2}$%     #m<sub>-2</sub>#  *)
(** printing m16  %$m_{16}$%     #m<sub>16</sub># *)

(** printing oplus %$\oplus$%    #⊕#  *)

Require Import Verse.
Require Import Verse.CryptoLib.sha2.
Require Import List.
Import ListNotations.

Import Nat.


(** * SHA2 hashing algorithm.

We give a common iterator for both the sha512 and sha256 algorithm. It
is implemented as a module parameterised over the configuration
module.

*)
Module SHA2 (C : CONFIG).

  Import C.

  Definition Word  := word WordSize.

  Definition Hash  := Array HASH_SIZE  hostE Word.
  Definition Block := Array BLOCK_SIZE bigE Word.


  (** Some helper inequalities *)

  Definition zltBlockSize : 0 < BLOCK_SIZE.
    unfold BLOCK_SIZE. repeat constructor.
  Defined.


  Definition nonZeroBlockSize : BLOCK_SIZE <> 0.
    unfold BLOCK_SIZE. eauto.
  Defined.



  Section Program.

    Variable v : VariableT.
    Arguments v [k] _.



    (** ** Program variables.

        The standard idiom of verse is to declare the parameters,
        local variables, and register variables in that order.

     *)

    (** *** Parameters

        SHA2 hashes are Merkel-Damgrad hash. The block iterator is
        only expected to compress the blocks and issues like padding
        is to be handled separately by the calling function.  Hence
        the iterator only needs the hash of the previous blocks to
        continue processing blocks. Thus there is only one parameter
        for the hash function namely the hash of the previous block.
     *)

    Variable hash : v Hash.

    Definition parameters : Declaration := [ Var hash ]%vector.

    (** *** Local variables.

        We keep the current block in a set of local variables. When
        compiling the resulting C code to a register rich machine, all
        of them could be allocated in registers and thus could be
        faster.

     *)

    Variable w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : v Word.

    Definition message_variables
      := [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]%vector.
    Definition locals : Declaration := Vector.map (fun x => Var x) message_variables.
    Definition W : VarIndex v BLOCK_SIZE Word := varIndex message_variables.
    Definition LOAD_BLOCK (blk : v Block) := loadCache blk W.

    (** * Message scheduling *)

    (** ** The state and temporary variables.

        We choose to put them in registers as there are the variables
        that are frequently used.

     *)


    Variable a b c d e f g h : v Word.
    Variable t               : v Word.

    Definition state_variables := [ a ; b ; c ; d ; e ; f ; g ; h ]%vector.

    Definition registers : Declaration :=
      Vector.map (fun x => Var x) (Vector.append state_variables [ t ]%vector).


    Definition STATE : VarIndex v HASH_SIZE Word := varIndex state_variables.
    Definition LOAD_STATE : code v := loadCache hash STATE.


    (** * Message scheduling.

        The block [w0,...,w15] is expanded to a message schedule
        [m(r)] given by the recurrence equation.

        [ m(r) = m(r - 16) + m(r - 7) + sigma0 m(r - 15) + sigma1 m(r - 2) ]

        where the [sigma0] and [sigma1] functions are of the form.


        [ sigma(x) = RotR(x, r0) oplus RotR(x, r1) oplus ShiftR(x, s)]
        *)

    Section MessageSchedule.

      (** We give the message schedule calculation for the ith message
          index. Since the recurrence relation governing m(r) refers
          only to BLOCK_SIZE many previous values, rather than computing
          the sequence m(r) in separate variables we reuse the [w]
          varaibles by placing m(r) in [w(r mod BLOCK_SIZE)] *)


      Variable idx   : nat.
      Variable idxPf : idx < BLOCK_SIZE.


      (** Function to increment message index *)
      Definition nextIdx : { sIdx : nat | sIdx < BLOCK_SIZE } :=
        if idx =? 15 then @exist _ _ 0 zltBlockSize
        else let sIdx := S idx in
             @exist _ _
                   (sIdx mod BLOCK_SIZE)
                   (PeanoNat.Nat.mod_upper_bound sIdx BLOCK_SIZE nonZeroBlockSize).

      Definition M  : v Word.
        verse (W[- idx -]).
      Defined.

      (** We capture m(idx - j) using this variable *)
      Definition MM (j : nat) : v Word.
        verse (W [- (idx + 16 - j) mod BLOCK_SIZE -]).
      Defined.


      (** We now give the code for updating the message M with the value
          of the appropriate sigma function.
       *)

      Definition sigma (r0 r1 s : nat)(x : v Word) : expr v Word :=
        (x >>> r1) XOR (x >>> r0) XOR (x >> s).

      Definition SCHEDULE :=
        let sigma0 := sigma r00 r01 s0 (MM 15) in
        let sigma1 := sigma r10 r11 s1 (MM 2) in
        [ M ::=+ MM 7 + sigma0 + sigma1].
    End MessageSchedule.

    Lemma correctnessNextIdx : forall n, proj1_sig (nextIdx n) = S n mod BLOCK_SIZE.
      intro n.
      do 16 (destruct n; trivial).
    Qed.


    (** * Sha2 round.

      The Sha2 hash function keeps track of a state in the variables
      a-h, and updates the state according to the equation.


      <<
      a' = t1 + t2
      b' = a
      c' = b
      d' = c
      e' = d + t1
      f' = e
      g' = f
      h' = g
      >>
      where


      [t1 = h + k + m + Sigma1(e) + CH e f g]
      [t2 = Sigma0(a) + MAJ a b c]


      where the [Sigma] functions are of the form
      [Sigma(x) = RotR(x , r0) oplus RotR(x,r1) oplus RotR(x,r2)]

      We capture the state as a record of variables.

     *)

    Record State := { A : v Word;
                      B : v Word;
                      C : v Word;
                      D : v Word;
                      E : v Word;
                      F : v Word;
                      G : v Word;
                      H : v Word;
                     }.

    (** The starting state *)
    Definition state0 : State:=
      {| A := a;
         B := b;
         C := c;
         D := d;
         E := e;
         F := f;
         G := g;
         H := h;
       |}.


    (** Instead of using different variables for each round we just
        update the state by permuting elements
     *)

    Definition newState (s : State):=
      {|
        A := H s;
        B := A s;
        C := B s;
        D := C s;
        E := D s;
        F := E s;
        G := F s;
        H := G s
      |}.


    Definition Sigma r0 r1 r2 (x : v Word) : expr v Word :=
      (x >>> r2) XOR (x >>> r1) XOR (x >>> r0).

    Definition Sigma0 (s : State) := Sigma R00 R01 R02 (A s).
    Definition Sigma1 (s : State) := Sigma R10 R11 R12 (E s).


    (** The CH and the MAJ functions are also defined computing their result
        into the temp variable temp
     *)

    Definition CH (B C D : v Word) : expr v Word :=
      (D XOR (B AND (C XOR D))). (* === (B AND C) XOR (neg B and D)  *)

    Definition MAJ (B C D : v Word) : expr v Word :=
      (B AND C) OR (D AND (C OR B)). (* ==== (B AND C) OR (C AND D) OR (B AND D) *)


    (** The heart of the hash algorithm a single round where we update
        the state held in the variables [a b c d e f g h] according to
        the procedure STEP. This step requires the message word [M]
        applicable for that round computed the message schedule, and
        the round constant [K].
     *)
    Definition STEP (s : State)(M : v Word)(K : constant Word) : code v :=
      [ t ::= H s + K + M + CH (E s) (F s) (G s) + Sigma1 s;
        D s ::=+ t;
        H s ::= t + Sigma0 s + MAJ (A s) (B s) (C s)
      ].

    (** Having defined the [STEP] we look at a single round. A round
        [r] consists of an application of the [STEP] together with
        modifying the message for use in round [r +
        BLOCK_SIZE]. However, the last [BLOCK_SIZE] many rounds need
        not to update the message word as they are not going to be
        used. We now describe the two variants.  *)

    Definition ROUND_WITH_SCHEDULE stAndIdx K :=
      match stAndIdx with
      | (st, @exist _ _ mIdx mIdxBoundPf) =>
        let Mesg := M mIdx mIdxBoundPf in
        STEP st Mesg K ++ SCHEDULE mIdx mIdxBoundPf
      end.

    Definition ROUND_WITHOUT_SCHEDULE stAndIdx K :=
      match stAndIdx with
      | (st, @exist _ _ mIdx mIdxBoundPf) =>
        let Mesg := M mIdx mIdxBoundPf in
        STEP st Mesg K
      end.


    Section GenerateRounds.

      Definition MessageIndex  := { r : nat | r < BLOCK_SIZE}.
      Definition Accumulator := (State * MessageIndex)%type.
      Definition next (acc : Accumulator) :=
        match acc with
        | (s, @exist _ _ idx _) => (newState s, nextIdx idx)
        end.

      Variable genCode : Accumulator -> constant Word -> code v.

      Fixpoint generateRounds (acc : Accumulator) (Ks : list (constant Word))
        : code v * Accumulator
        := match Ks with
           | k :: ks =>
             let cde := genCode acc k in
             let (cdeRest, stp) := generateRounds (next acc) ks in
             (cde ++ cdeRest, stp)
           | [] => ([],acc)
           end.
    End GenerateRounds.


    Fixpoint splitAt {A}(n : nat)(l : list A) : list A * list A :=
      match l,n with
      | x::xs, S m => match splitAt m xs with
                        (ys,zs) => (x :: ys, zs)
                      end

      | _      , _ => ([ ],l)
      end.

    Definition ALL_ROUNDS :=
      let Ks := Vector.to_list KVec in
      let (KsInit, KsLast) := splitAt (ROUNDS - BLOCK_SIZE)  Ks in
      let acc0 := (state0, @exist _ _ 0 zltBlockSize) in
      let (cd1, acc1) := generateRounds ROUND_WITH_SCHEDULE acc0 KsInit in
      let (cd2,_) := generateRounds ROUND_WITHOUT_SCHEDULE acc1 KsLast in
      cd1 ++ cd2.


    Definition UPDATE_ITH (i : nat) (pf : i < HASH_SIZE) : code v.
      verse ([ STATE[- i -] ::=+ hash [- i -]]).
    Defined.

    Definition UPDATE : code v
      := foreach (indices hash) UPDATE_ITH ++ moveBackCache hash STATE.

    Definition sha2 : iterator v Block :=
      {|
        setup   := LOAD_STATE;
        process := fun block => (LOAD_BLOCK block
                                         ++ ALL_ROUNDS
                                         ++ UPDATE);
        finalise := [ ]
      |}.
  End Program.
End SHA2.
