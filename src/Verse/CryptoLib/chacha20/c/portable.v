(**

This module implements the following

- The encryption iterator for ChaCha20 and XChaCha20.

- A host-endian variant of the chacha20 keystream meant for use in
  csprg.

*)

Require Import Verse.
Require Import Verse.Arch.C.
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
    Variable xiv      : progvar XIV.
    Variable ctrRef   : progvar (Array 1 hostE Counter).

    Definition parameters : Declaration
      := [Var key; Var iv; Var ctrRef].

    Definition xparameters : Declaration
      := [Var key; Var xiv; Var ctrRef].

    (* We do not have local stack variables *)
    Definition stack : Declaration    := Empty.

    (**
       Besides we have the following in registers

       - The 4x4 state matrix in x0,...,x16

       - A register copy of the counter

       - A temporary register

   *)

    Variable x0  x1  x2  x3
             x4  x5  x6  x7
             x8  x9  x10 x11
             x12 x13 x14 x15 : progvar Word.
    Variable ctr             : progvar Counter.
    Variable Temp            : progvar Word.

    (**
        Let us make some auxiliary definitions that simplify some of
        the variable manipulations.

     *)
    Definition stateVars := [ x0; x1; x2; x3;
                              x4; x5; x6; x7;
                              x8; x9; x10; x11;
                              x12; x13; x14; x15
                            ].

    (** The register variables required by the cipher *)
    Definition registers  := Vector.map Var (Vector.append [ctr; Temp] stateVars).

    (** The registers required by the key stream generator *)

    Definition csprgRegisters := Vector.map Var ( ctr :: stateVars ).
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
      := [ a ::=+ b; d ::=^ a; d ::=<<< 16;
           c ::=+ d; b ::=^ c; b ::=<<< 12;
           a ::=+ b; d ::=^ a; d ::=<<< 8;
           c ::=+ d; b ::=^ c; b ::=<<< 7
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

    Definition ComputeStream := List.concat [ Init; Rounds; Update].

    (** ** The Encryption and the keystream.

        Recall that this module serves as the base for two different
        implementations, the first being the chacha20 encryption and
        the other being the keystream for csprg. We define the block
        transformation for each of the case above.

     *)

    Definition XorBlock (B : progvar (Block littleE))(i : nat) (_ : i < 16)
      : code progvar.
      verse [ Temp ::= B[- i -]; Temp ::=^ X [- i -]; MOVE Temp TO B[- i -] ].
    Defined.

    Definition EmitStream (B : progvar (Block hostE))(i : nat) (_ : i < 16)
      : code progvar.
      verse [ MOVE (X i _) TO B[- i -] ].
    Defined.

    Definition Encrypt blk
      := (ComputeStream ++ foreach (indices blk) (XorBlock blk)
                        ++ [ ++ ctr ])%list.

    Definition CSPRGStream blk
      := (ComputeStream ++ foreach (indices blk) (EmitStream blk)
                        ++ [ ++ ctr ])%list.

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

    Definition EncryptIterator : iterator (Block littleE) progvar :=
      {| setup    := LoadCounter;
         process  := Encrypt;
         finalise := StoreCounter
      |}.

    Definition CSPRGIterator : iterator (Block hostE) progvar :=
      {| setup    := LoadCounter;
         process  := CSPRGStream;
         finalise := StoreCounter
      |}.

  End ChaCha20.

  (* ** Generating the C code.

    We start by defining the variables to use for the C code.

   *)

  Definition wordTy    : CType direct := recover (typeDenote Word).
  Definition counterTy : CType direct := recover (typeDenote Counter).

  Definition regVars
    := (- cr wordTy "x0",  cr wordTy "x1",  cr wordTy "x2",  cr wordTy "x3",
          cr wordTy "x4",  cr wordTy "x5",  cr wordTy "x6",  cr wordTy "x7",
          cr wordTy "x8",  cr wordTy "x9",  cr wordTy "x10", cr wordTy "x11",
          cr wordTy "x12", cr wordTy "x13", cr wordTy "x14", cr wordTy "x15",
          cr counterTy "ctr", cr wordTy "Tmp"
       -).

  Definition csprgVars
    := (- cr wordTy "x0",  cr wordTy "x1",  cr wordTy "x2",  cr wordTy "x3",
          cr wordTy "x4",  cr wordTy "x5",  cr wordTy "x6",  cr wordTy "x7",
          cr wordTy "x8",  cr wordTy "x9",  cr wordTy "x10", cr wordTy "x11",
          cr wordTy "x12", cr wordTy "x13", cr wordTy "x14", cr wordTy "x15",
          cr counterTy "ctr"
       -).

  (** The prototype and the code for the chacha20 encryption routine *)
  Definition prototype_encrypt (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.iteratorPrototype (Block littleE) fname parameters.
  Defined.


  Definition implementation_encrypt (fname : string) : Doc  + {Compile.CompileError}.
    Compile.iterator (Block littleE) fname parameters stack registers.
    assignRegisters regVars.
    statements EncryptIterator.
  Defined.


  (** The prototype and the code for chacha20 csprg routine *)

  Definition prototype_csprg (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.iteratorPrototype (Block hostE) fname parameters.
  Defined.

  Definition inplementation_csprg (fname : string) : Doc  + {Compile.CompileError}.
    Compile.iterator (Block hostE) fname parameters stack csprgRegisters.
    assignRegisters csprgVars.
    statements CSPRGIterator.
  Defined.


  (** The combined source code and prototypes. *)
  Definition encryptName (fname : string) := fname.
  Definition csprgName   (fname : string) := (fname ++ "_keystream")%string.

  Definition implementation (fname : string) : Doc + {Compile.CompileError} :=
    encrypt <- implementation_encrypt (encryptName fname);
      csprg  <- implementation_encrypt (csprgName fname);
      {- vcat [encrypt; csprg] -}.

  Definition prototypes fname :=
    encryptProto <- prototype_encrypt (encryptName fname);
     csprgProto <- prototype_csprg (csprgName fname);
      {- [ encryptProto ; csprgProto ]%list -}.

End Internal.

(** Stuff to generate the C file and the raaz FFI call stubs

*)

Require Import Verse.Extraction.Ocaml.
Require Import Verse.CryptoLib.Names.
Definition implementation_name : Name := {| primitive := "chacha20";
                                            arch      := "c";
                                            features  := ["portable"]
                                         |}.

  Definition cname     := cFunName implementation_name.
  Definition cfilename := libVerseFilePath implementation_name.


Definition implementation : unit
  := writeProgram (C cfilename) (Internal.implementation cname).

Definition prototypes := recover (Internal.prototypes cname).

Require Import Verse.FFI.Raaz.

Definition raazFFI : unit :=
  let module := raazModule implementation_name in
  write_module module (List.map ccall prototypes).
