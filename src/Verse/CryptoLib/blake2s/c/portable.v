Require Import Verse.
Require Import Verse.CryptoLib.blake2.
Require Import Verse.CryptoLib.blake2.c.portable.

Require Vector.
Import Vector.VectorNotations.

Module Config <: CONFIG.

  Definition WORD_LOG_SIZE := 2.
  Definition ROUNDS        := 10.
  Definition IVVec          :=
    [
     Ox "6a09e667";
     Ox "bb67ae85";
     Ox "3c6ef372";
     Ox "a54ff53a";
     Ox "510e527f";
     Ox "9b05688c";
     Ox "1f83d9ab";
     Ox "5be0cd19"
    ].

  (** The rotation constants used by the G function *)
  Definition R0 := 16.
  Definition R1 := 12.
  Definition R2 := 8.
  Definition R3 := 7.


End Config.



Module Blake2s := Blake2 (Config).
Require Import Verse.Target.C.

Inductive name := verse_blake2s_c_portable_iter | verse_blake2s_c_portable_last.

Require Verse.CryptoLib.blake2.


Module Allocation.

  Definition cword := uint32_t.

  Axiom blockPtr : cvar (ptrToArray blake2.BLOCK_SIZE cword).
  Axiom nBlocks  : cvar uint64_t.
  Axiom UpperRef LowerRef : cvar (array 1 cword).

  Axiom lastBlock : cvar (array blake2.BLOCK_SIZE cword).
  Axiom nBytes   : cvar uint64_t.
  Axiom Upper Lower : cvar cword.
  Axiom f0 f1 : cvar cword.

  Axiom hash     : cvar (ptrToArray blake2.HASH_SIZE cword).
  Axiom h0 h1 h2 h3 h4 h5 h6 h7 : cvar cword.
  Axiom w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : cvar cword.
  Axiom v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : cvar cword.
  Axiom C LMSB U L : cvar cword.
End Allocation.

Export Allocation.

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


Definition blake2sIter
  := Compile.Iterator verse_blake2s_c_portable_iter
                      Blake2s.Block
                      Blake2s.paramIterator
                      Blake2s.stack
                      Blake2s.regIterator
                      blockPtr
                      nBlocks
                      params
                      locals
                      registers
                      Blake2s.Iterator.

Definition blake2sLast
  := Compile.Function verse_blake2s_c_portable_last
                      Blake2s.paramLastBlock
                      Blake2s.stack
                      Blake2s.regLastBlock
                      paramsLast
                      locals
                      registersLast
                      Blake2s.LastBlockCompress.

Require Import Verse.Error.
Definition iterator   : Compile.programLine := recover (blake2sIter).
Definition lastchunk  : Compile.programLine := recover (blake2sLast).
Definition program := verseC [iterator; lastchunk].

Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI
  := ffi [ iterator verse_blake2s_c_portable_iter
                    Blake2s.Block
                    Blake2s.paramIterator;
           function verse_blake2s_c_portable_last
                    Blake2s.paramLastBlock
         ].

(*

Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.
Goal to_print programLast.
  print.
Abort.

*)
