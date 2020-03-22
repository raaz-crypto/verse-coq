Require Import Verse.
Require Import Verse.CryptoLib.blake2.
Require Import Verse.CryptoLib.blake2.c.portable.

Require Vector.
Import Vector.VectorNotations.

Module Config <: CONFIG.

  Definition WORD_LOG_SIZE := 3.
  Definition ROUNDS        := 12.
  Definition IVVec          :=
    [
      Ox "6a09e667f3bcc908";
      Ox "bb67ae8584caa73b";
      Ox "3c6ef372fe94f82b";
      Ox "a54ff53a5f1d36f1";
      Ox "510e527fade682d1";
      Ox "9b05688c2b3e6c1f";
      Ox "1f83d9abfb41bd6b";
      Ox "5be0cd19137e2179"
    ].
  (** The rotation constants used by the G function *)
  Definition R0 := 32.
  Definition R1 := 24.
  Definition R2 := 16.
  Definition R3 := 63.


End Config.


Module Blake2b := Blake2 (Config).
Require Import Verse.Target.C.

Inductive name := verse_blake2b_c_portable_iter |verse_blake2b_c_portable_last.
Require Verse.CryptoLib.blake2.


Module Allocation.
  Axiom blockPtr  : cvar (ptrToArray blake2.BLOCK_SIZE uint64_t).
  Axiom nBlocks  : cvar uint64_t.
  Axiom UpperRef LowerRef : cvar (array 1 uint64_t).

  Axiom lastBlock : cvar (array blake2.BLOCK_SIZE uint64_t).
  Axiom nBytes   : cvar uint64_t.
  Axiom Upper Lower : cvar uint64_t.
  Axiom f0 f1 : cvar uint64_t.

  Axiom hash     : cvar (ptrToArray blake2.HASH_SIZE uint64_t).


  Axiom h0 h1 h2 h3 h4 h5 h6 h7 : cvar uint64_t.
  Axiom w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : cvar uint64_t.
  Axiom v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : cvar uint64_t.
  Axiom C LMSB U L : cvar uint64_t.
End Allocation.

Import Allocation.

Definition params     := (- UpperRef , LowerRef , hash -).
Definition paramsLast := (- lastBlock, nBytes, Upper, Lower, f0, f1, hash -).

Definition locals     := (- h0 , h1 , h2 , h3 , h4 , h5 , h6 , h7 -).

Definition registers  :=
  (- w0 , w1 , w2 , w3 , w4 , w5 , w6 , w7 , w8 , w9 , w10 , w11 , w12 , w13,  w14 ,  w15 ,
     v0 , v4 , v8 , v12,
     v1 , v5 , v9 , v13,
     v2 , v6 , v10, v14,
     v3 , v7 , v11, v15,
     C, LMSB, U, L
  -).

Definition registersLast  :=
  (- w0 , w1 , w2 , w3 , w4 , w5 , w6 , w7 , w8 , w9 , w10 , w11 , w12 , w13,  w14 ,  w15 ,
     v0 , v4 , v8 , v12,
     v1 , v5 , v9 , v13,
     v2 , v6 , v10, v14,
     v3 , v7 , v11, v15,
     C, LMSB
  -).


Definition blake2bIter
  := Compile.Iterator verse_blake2b_c_portable_iter
                      Blake2b.Block
                      Blake2b.paramIterator
                      Blake2b.stack
                      Blake2b.regIterator
                      blockPtr
                      nBlocks
                      params
                      locals
                      registers
                      Blake2b.Iterator.


Definition blake2bLast
  := Compile.Function verse_blake2b_c_portable_last
                      Blake2b.paramLastBlock
                      Blake2b.stack
                      Blake2b.regLastBlock
                      paramsLast
                      locals
                      registersLast
                      Blake2b.LastBlockCompress.

Require Import Verse.Error.
Definition iterator   : Compile.programLine := recover (blake2bIter).
Definition lastBlock  : Compile.programLine := recover (blake2bLast).
Definition program := verseC [iterator; lastBlock].

(*

Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.
Goal to_print program.
  print.
Abort.

*)
