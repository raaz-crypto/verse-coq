Require Import Verse.
Require Import Verse.CryptoLib.blake2.
Require Import Verse.CryptoLib.blake2.c.portable.

Require Vector.
Import Vector.VectorNotations.

Module Config <: CONFIG.

  Definition Word   := Word32.
  Definition ROUNDS := 10.
  Definition IVVec  :=
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

Definition blake2sIter
  := CIterator verse_blake2s_c_portable_iter
                      Blake2s.Block
                      Blake2s.paramIterator
                      Blake2s.stack
                      Blake2s.regIterator
                      Blake2s.Iterator.

Definition blake2sLast
  := CFunction verse_blake2s_c_portable_last
                      Blake2s.paramLastBlock
                      Blake2s.stack
                      Blake2s.regLastBlock
                      Blake2s.LastBlockCompress.

Require Import Verse.Error.
Definition iterator   : Compile.programLine := recover (blake2sIter).
Definition lastchunk  : Compile.programLine := recover (blake2sLast).
Definition program := verseC [iterator; lastchunk].

Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name} (name : Name)
  := mkProgram name [ iterator verse_blake2s_c_portable_iter
                               Blake2s.Block
                               Blake2s.paramIterator;
                      function verse_blake2s_c_portable_last
                               Blake2s.paramLastBlock
                    ].

Arguments raazFFI [Name].

(*

Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.
Goal to_print blake2sLast.
  print.
Abort.

*)
