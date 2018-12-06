Require Import Verse.
Require Import Verse.CryptoLib.sha2.
Require Import Verse.Semantics.
Import StandardTactics.
Require Import Verse.WordFacts.
Require Import Verse.WordRing.
Open Scope word_scope.

Import NArith.
Import Nat.
Require Vector.
Import VectorNotations.
Require Import List.
Import ListNotations.

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
  Hint Resolve NPeano.Nat.lt_0_succ.
  Definition zltBlockSize : 0 < BLOCK_SIZE.
    unfold BLOCK_SIZE. eauto.
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
    Definition locals : Declaration := Vector.map Var message_variables.
    Definition W : VarIndex v BLOCK_SIZE Word := varIndex message_variables.
    Definition LOAD_BLOCK (blk : v Block) := loadCache blk W.

    (** * Message scheduling *)

    (** ** The state and temporary variables.

        We choose to put them in registers as there are the variables
        that are frequently used.

     *)


    Variable a b c d e f g h : v Word.
    Variable t tp temp       : v Word.

    Definition state_variables := [ a ; b ; c ; d ; e ; f ; g ; h ]%vector.

    Definition registers : Declaration :=
      Vector.map Var (Vector.append state_variables [ t ; tp ; temp]%vector).


    Definition STATE : VarIndex v HASH_SIZE Word := varIndex state_variables.
    Definition LOAD_STATE : code v := loadCache hash STATE.


    (** * Message scheduling.

        The block [w0,...,w15] is expanded to a message schedule
        [m(r)] given by the recurrence equation.

        [ m(r) = m(r - 16) + m(r - 7) + σ₀ m(r - 15) + σ₁ m(r - 2) ]

        where the σ₀ and σ₁ functions are of the form.


        [ σ(x) = RotR(x, r0) ⊕ RotR(x, r1) ⊕ ShiftR(x, s)]
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
      Definition nextIdx : { sIdx | sIdx < BLOCK_SIZE } :=
        if idx =? 15 then @exist _ _ 0 zltBlockSize
        else let sIdx := S idx in
             @exist _ _
                   (sIdx mod BLOCK_SIZE)%nat
                   (NPeano.Nat.mod_upper_bound sIdx BLOCK_SIZE nonZeroBlockSize).

      Definition M  := W idx idxPf.

      (** We capture m(idx - j) using this variable *)
      Definition MM (j : nat) : v Word.
        verse (W ((idx + 16 - j) mod BLOCK_SIZE) _)%nat.
      Defined.


      (** We now give the code for updating the message M with the value
          of the appropriate sigma function.
       *)
      Definition sigma (r0 r1 s : nat)(x : v Word) :=
        [ temp ::= x >>> r1; tp ::= x >>> r0;
          temp ::=^ tp;      tp ::= x >> s;
          temp ::=^ tp; M ::=+ temp
        ]%list.

      Definition SCHEDULE :=
        let sigma0 := sigma r00 r01 s0 (MM 15) in
        let sigma1 := sigma r10 r11 s1 (MM 2) in
        [ M ::=+ MM 7 ] ++ sigma0 ++ sigma1.
      (** This completes the code for message scheduling *)
    End MessageSchedule.

    Lemma correctnessNextIdx : forall n, proj1_sig (nextIdx n) = (S n mod BLOCK_SIZE)%nat.
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

      <<
      t1 = h + k + m + 𝚺₁(e) + CH e f g
      t2 = 𝚺₀(a) + MAJ a b c
      >>

      where the 𝚺 functions are of the form
      𝚺 (x) = RotR(x , r0) ^ RotR(x,r1) ^ RotR(x,r2)
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

    Definition sig r0 r1 r2 (x : typeDenote Word : Type) :=
      x RotR r2 XOR x RotR r1 XOR x RotR r0.

    Definition Sigma r0 r1 r2 (x : v Word) :=
      [ temp ::= x >>> (r2 - r1); temp ::=^ x;
        temp ::=>>> (r1 - r0);    temp ::=^ x;
        temp ::=>>> r0;
        ASSERT Val temp = sig r0 r1 r2 (Val x)
      ]%list.

    Definition Sigma0 (s : State) := Sigma R00 R01 R02 (A s).
    Definition Sigma1 (s : State) := Sigma R10 R11 R12 (E s).


    (** The CH and the MAJ functions are also defined computing their result
        into the temp variable temp
     *)

    Definition CH (s : State) : code v:=
            [ tp ::=~ E s;
              tp ::=& G s;
              temp ::= E s & F s; temp ::=^ tp;
              ASSERT E s HAS e; F s HAS f; G s HAS g
              IN
              Val temp = (e AND f) XOR (NOT e AND g)
            ]%list.

    Definition MAJ (s : State) : code v :=
      [ temp  ::=  B s | C s;
        temp  ::=& A s;
        tp    ::=  B s & C s;
        temp  ::=| tp;
        ASSERT A s HAS a; B s HAS b; C s HAS c
        IN
        Val temp = (a AND b) OR (a AND c) OR (b AND c)
      ].

    (** The heart of the hash algorithm a single round where we update
        the state held in the variables [a b c d e f g h] according to
        the procedure STEP. This step requires the message word [M]
        applicable for that round computed the message schedule, and
        the round constant [K].
     *)
    Definition STEP (s : State)(M : v Word)(K : constant Word) : code v :=
      [ t ::= H s + K  ;  t ::=+ M ]
        ++ CH s        (* temp = CH e f g *)
        ++ [ t ::=+ temp ]
        ++  Sigma1 s   (* temp =  σ₁(e)   *)
        ++ [ t ::=+ temp ]
        ++ [ D s ::=+ t ]
        ++ Sigma0 s    (* temp =  σ₀(a) *)
        ++ [ t ::=+ temp ]
        ++ MAJ s       (* temp = MAJ a b c *)
        ++ [ H s ::= temp + t ] (* h =  t + MAJ a b c *)
        ++ [ ASSERT A s HAD a; B s HAD b; C s HAD c; D s HAD d;
                    E s HAD e; F s HAD f; G s HAD g; H s HAD h
             IN
             let s' := newState s in
             let S1 := sig R10 R11 R12 e in
             let ch := (e AND f) XOR (NOT e AND g) in
             let temp1 := h + S1 + ch + [[K]] + Val M in
             let S0 := sig R00 R01 R02 a in
             let maj := (a AND b) OR (a AND c) OR (b AND c) in
             let temp2 := S0 + maj in

             Val (H s') = g
             /\ Val (G s') = f
             /\ Val (F s') = e
             /\ Val (E s') = d + temp1
             /\ Val (D s') = c
             /\ Val (C s') = b
             /\ Val (B s') = a
             /\ Val (A s') = temp1 + temp2
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
        | (s,@exist _ _ idx _) => (newState s, nextIdx idx)
        end.

      Variable genCode : Accumulator -> constant Word -> code v.

      Fixpoint generateRounds (acc : Accumulator) (Ks : list (constant Word))
        : code v * Accumulator
        := match Ks with
           | k :: ks =>
             let cde := genCode acc k in
             let (cdeRest, stp) := generateRounds (next acc) ks in
             (cde ++ cdeRest, stp)
           | [ ] => ([ ],acc)
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
      verse ([STATE i _ ::=+ hash [- i -]]).
    Defined.

    Definition UPDATE : code v
      := foreach (indices hash) UPDATE_ITH ++ moveBackCache hash STATE.

    Definition sha2 : iterator Block v :=
      {|
        setup   := LOAD_STATE;
        process := fun block => (LOAD_BLOCK block
                                         ++ ALL_ROUNDS
                                         ++ UPDATE);
        finalise := [ ]
      |}.
  End Program.

  (* Write a scoped version of STEP *)
  Definition scSTEP v t tp temp a b c d e f g h m k
    := STEP v t tp temp {| A := a; B := b; C := c; D := d; E := e; F := f; G := g; H := h |} m k.

  (* Extract the proof obligation from scSTEP *)
  Definition toProve : Prop.
    exParamProp scSTEP.
  Defined.

  (* A lemma for correctness of the Sigma optimization *)
  Lemma SigmaCorrect r0 r1 r2 (incr : r0 <= r1 <= r2) (w : typeDenote Word : Type)
    : RotRW r0 (XorW (RotRW (r1 - r0) (XorW (RotRW (r2 - r1) w) w)) w) =
      XorW (XorW (RotRW r2 w) (RotRW r1 w)) (RotRW r0 w).
  Proof.
    repeat rewrite rotRDistrXor;
      repeat rewrite rotRCompose;
      repeat rewrite Minus.le_plus_minus_r;
      easy.
  Qed.

  Definition proof : toProve.
    simplify.
    (* Sigma *)
    apply SigmaCorrect. apply increasing_R's.
    (* Sigma *)
    apply SigmaCorrect. apply increasing_R's.
    (* Maj *)
    rewrite AndComm.
    now rewrite AndDistrOr.
    (* Ring *)
    rewrite H3.
    Add Ring Here : (mod_semi_ring (4 * (2 * (2 ^ WordSize)))).
    now ring_simplify.

    rewrite H3.
    rewrite H2.
    rewrite H1.
    now ring_simplify.
  Qed.

End SHA2.
