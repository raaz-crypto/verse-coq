(**

This module implements the following

- The encryption iterator for ChaCha20 and XChaCha20.

- A host-endian variant of the chacha20 keystream meant for use in
  csprg.

*)

Require Import Verse.
Require Import Verse.CryptoLib.chacha20.common.

Module Internal.

  Section ChaCha20.

    (** ** Program variables.

    Following the standard idiom, we start by abstracting over the
    program variables

     *)

    Variable progvar  : VariableT.
    Arguments progvar [k] _.

    (**

       The chacha20 round function takes the key, iv, and the
       counter. The xchacha20 variant uses an extended iv which is
       captured by the [xiv] variable.

     *)

    Variable key      : progvar Key.
    Variable iv       : progvar IV.
    Variable ctrRef   : progvar (Array 1 hostE Counter).

    (** IV for hchacha20 *)
    Variable hiv0 hiv1 hiv2 hiv3 : progvar Word.

    Definition parameters : Declaration
      := [Var key; Var iv; Var ctrRef].

    Definition hparameters : Declaration
      := [Var key; Var hiv0; Var hiv1; Var hiv2; Var hiv3].

    (* We do not have local stack variables *)
    Definition stack : Declaration    := [].

    (**
       Besides we have the following in registers

       - The 4x4 state matrix in x0,...,x16

       - A register copy of the counter

       - A temporary register

   *)

    Variable Temp            : progvar Word.
    Variable ctr             : progvar Counter.
    Variable x0  x1  x2  x3
             x4  x5  x6  x7
             x8  x9  x10 x11
             x12 x13 x14 x15 : progvar Word.

    (**
        Let us make some auxiliary definitions that simplify some of
        the variable manipulations.

     *)
    Definition stateVars := [ x0; x1; x2; x3;
                              x4; x5; x6; x7;
                              x8; x9; x10; x11;
                              x12; x13; x14; x15
                            ].

    (** The registers required for HCHaCha20 hash *)
    Definition hregisters := Vector.map (fun x => Var x) stateVars.

    (** The registers required by the key stream generator *)
    Definition csprgRegisters := Var ctr :: hregisters.

    (** The register variables required by the cipher *)
    Definition registers  := Var Temp :: csprgRegisters.

    (** It is useful to have a uniform way to index the state variables. *)

    Definition X : VarIndex progvar 16 Word := varIndex stateVars.


    (** ** The chacha20 keystream.

        The chacha20 cipher consists of computing a key stream which
        is then xor-ed to the input stream to get the encrypted
        stream. Computation of the key stream is done by transforming
        the state matrix as follows (the bits in the state matrix
        becomes the key stream)

        - Initialisation of the state.

        - Apply 20 rounds of the chacha20 round function.

        - Update the state by adding the initial value of the state.

     *)

    (** *** The initialisation.

       The initial state is computed as follows.

    *)

    Definition Init : code progvar.
      verse [
          x0  ::= C0         ; x1  ::= C1         ; x2  ::= C2         ; x3  ::= C3;
          x4  ::= key[- 0 -] ; x5  ::= key[- 1 -] ; x6  ::= key[- 2 -] ; x7 ::= key[- 3 -];
          x8  ::= key[- 4 -] ; x9  ::= key[- 5 -] ; x10 ::= key[- 6 -] ; x11 ::= key[- 7 -];
          x12 ::= ctr        ; x13 ::= iv[- 0 -]  ; x14 ::= iv[- 1 -]  ; x15 ::= iv[- 2 -]
        ].
    Defined.


    (** *** The chacha20 round.

     The rounds are defined in terms of the chacha20 quarter round

     *)

    Definition QRound (a b c d : progvar Word) : code progvar
      := [ a ::=+ b; d ::=x a; d ::= d <<< 16;
           c ::=+ d; b ::=x c; b ::= b <<< 12;
           a ::=+ b; d ::=x a; d ::= d <<< 8;
           c ::=+ d; b ::=x c; b ::= b <<< 7
         ].

    (**

       The 20 rounds that the algorithm performs, alternate between
       the _column round_ where we apply the quarter round on all the
       four columns and the _diagonal round_ where the quarter round
       is applied on each of the four diagonals. We code this up as 10
       double round where a double round consists of a column round
       and a diagonal round.

     *)

    Definition Rounds : code progvar :=
      let colRound := List.concat [ QRound x0 x4 x8   x12;
                                    QRound x1 x5 x9   x13;
                                    QRound x2 x6 x10  x14;
                                    QRound x3 x7 x11  x15
                                  ] in
      let diagRound := List.concat [ QRound x0 x5 x10 x15;
                                     QRound x1 x6 x11 x12;
                                     QRound x2 x7 x8  x13;
                                     QRound x3 x4 x9  x14
                                   ] in
      let doubleRound := (colRound ++ diagRound)%list
      in List.concat (List.repeat doubleRound 10).

    (** ** The state update.

        In the final step, we updated the transformed state by adding
        it to the initial state.

     *)
    Definition Update : code progvar.
      verse [
          x0  ::=+ C0         ; x1  ::=+ C1         ; x2  ::=+ C2         ; x3  ::=+ C3;
          x4  ::=+ key[- 0 -] ; x5  ::=+ key[- 1 -] ; x6  ::=+ key[- 2 -] ; x7  ::=+ key[- 3 -];
          x8  ::=+ key[- 4 -] ; x9  ::=+ key[- 5 -] ; x10 ::=+ key[- 6 -] ; x11 ::=+ key[- 7 -];
          x12 ::=+ ctr        ; x13 ::=+ iv[- 0 -]  ; x14 ::=+ iv[- 1 -]  ; x15 ::=+ iv[- 2 -]
        ].

    Defined.

    (** ** The chacha20 stream

        Putting all the code fragments together, we have the algorithm
        that compute the chacha20 stream inside the state matrix.

     *)

    Definition TransformState := List.concat [ Init; Rounds; Update].

    (** ** The XChaCha20 variant.

    The XChaCha20 cipher is a variant of the standard chacha20 cipher
    but supports a 192-bit (6x32-bit). With the iv being large, one
    can safely choose them at random and be confident of not repeating
    them ever --- the 96-bit iv that the standard supports is too
    small for such random choice and would often need to keep track of
    additional information to ensure that ivs are not repeated.

    This variant uses the following steps

    - It uses the HChaCha20 hashing to first initialise a key (which
      makes use of the first four words of the iv.

    - It then uses certain portion of the state and the rest of the
      two words as the key and iv for a chacha20 state.

     *)


    (** ** The Encryption and the keystream.

        Recall that this module serves as the base for two different
        implementations, the first being the chacha20 encryption and
        the other being the keystream for csprg. We define the block
        transformation for each of the case above.

     *)

    Definition XorBlock (B : progvar (Block littleE))(i : nat) (_ : i < 16)
      : code progvar.
      verse [ Temp ::= B[- i -]; Temp ::=x X [- i -]; MOVE Temp TO B[- i -] ].
    Defined.

    Definition EmitStream (B : progvar (Block hostE))(i : nat) (_ : i < 16)
      : code progvar.
      verse [ MOVE (X i _) TO B[- i -] ].
    Defined.

    Definition Encrypt blk
      := (TransformState ++ foreach (indices blk) (XorBlock blk)
                        ++ [ ctr ::=+ 1 ])%list.


    Definition CSPRGStream blk
      := (TransformState ++ foreach (indices blk) (EmitStream blk)
                         ++ [ ctr ::=+ 1 ])%list.

    (* ** The HChacha20 hash and XChacha20.

       The XChacha20 is a variant of chacha20 that uses a larger iv
       which allows us to use random ivs with out fear of
       collision. Remember that if key,iv pairs are repeated, it would
       compromise the encryption of chacha20. The XChacha20 uses the
       key and part of the iv to first set up a subkey using the
       HChacha20 hash. It then proceeds to compute the encryption
       using this subkey and the rest of the iv. This module also
       exposes the hchacha20 function that updates the key array with
       the subkey.

     *)
    Definition HInit : code progvar.
      verse [
          x0  ::= C0         ; x1  ::= C1         ; x2  ::= C2         ; x3  ::= C3;
          x4  ::= key[- 0 -] ; x5  ::= key[- 1 -] ; x6  ::= key[- 2 -] ; x7 ::= key[- 3 -];
          x8  ::= key[- 4 -] ; x9  ::= key[- 5 -] ; x10 ::= key[- 6 -] ; x11 ::= key[- 7 -];
          x12 ::= hiv0       ; x13 ::= hiv1       ; x14 ::= hiv2       ; x15 ::= hiv3
        ].
    Defined.

    Definition HUpdateKey : code progvar.
      verse [ MOVE x0  TO key [- 0 -];
              MOVE x1  TO key [- 1 -];
              MOVE x2  TO key [- 2 -];
              MOVE x3  TO key [- 3 -];
              MOVE x12 TO key [- 4 -];
              MOVE x13 TO key [- 5 -];
              MOVE x14 TO key [- 6 -];
              MOVE x15 TO key [- 7 -]
            ].
    Defined.

    Definition HChaCha20 : code progvar :=  List.concat [ HInit; Rounds; HUpdateKey ].

    (** ** The iterators.

        Finally we define the iterator code for both the chacha20
        encryption and the chacha20 host-endian key stream.

     *)
    Definition LoadCounter : code progvar.
      verse [ ctr ::= ctrRef[- 0 -] ].
    Defined.
    Definition StoreCounter : code progvar.
      verse [ MOVE ctr TO ctrRef[- 0 -] ].
    Defined.

    Definition EncryptIterator : iterator progvar (Block littleE) :=
      {| setup    := LoadCounter;
         process  := Encrypt;
         finalise := StoreCounter
      |}.

    Definition CSPRGIterator : iterator progvar (Block hostE) :=
      {| setup    := LoadCounter;
         process  := CSPRGStream;
         finalise := StoreCounter
      |}.


  End ChaCha20.

End Internal.



Require Import Verse.Target.C.

Inductive name := verse_chacha20_c_portable
                | verse_chacha20csprg_c_portable
                | verse_hchacha20_c_portable.

Definition chacha20_iter :=
  CIterator verse_chacha20_c_portable
            (common.Block littleE)
            Internal.parameters
            Internal.stack
            Internal.registers
            Internal.EncryptIterator.

Definition hchacha20_fun :=
  CFunction verse_hchacha20_c_portable
            Internal.hparameters
            Internal.stack
            Internal.hregisters
            Internal.HChaCha20.


Definition csprg_iter :=
  CIterator verse_chacha20csprg_c_portable
            (common.Block hostE)
            Internal.parameters
            Internal.stack
            Internal.csprgRegisters
            Internal.CSPRGIterator.


Require Import Verse.Error.


Definition chacha20  : Compile.programLine := recover chacha20_iter.
Definition hchacha20 : Compile.programLine := recover hchacha20_fun.
Definition csprg     : Compile.programLine := recover csprg_iter.

Definition program   := verseC [chacha20; hchacha20 ; csprg].

Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name} (name : Name)
  := mkProgram name [ iterator verse_chacha20_c_portable
                               (common.Block littleE)
                               Internal.parameters;
                      function verse_hchacha20_c_portable Internal.hparameters;
                      iterator verse_chacha20csprg_c_portable
                               (common.Block hostE)
                               Internal.parameters
                    ].

(*
Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.
Goal to_print raazFFI.
  print.
Abort.

 *)
