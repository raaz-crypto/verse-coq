Require Import Verse.
Require Import Verse.CryptoLib.sha2.
Require Import Verse.CryptoLib.sha2.c.portable.

Module Config <: CONFIG.
  Definition WordSize := 2 (*Word32*).
  Definition ROUNDS := 64.
  Definition KVec := [ Ox "428a2f98";
                       Ox "71374491";
                       Ox "b5c0fbcf";
                       Ox "e9b5dba5";
                       Ox "3956c25b";
                       Ox "59f111f1";
                       Ox "923f82a4";
                       Ox "ab1c5ed5";
                       Ox "d807aa98";
                       Ox "12835b01";
                       Ox "243185be";
                       Ox "550c7dc3";
                       Ox "72be5d74";
                       Ox "80deb1fe";
                       Ox "9bdc06a7";
                       Ox "c19bf174";
                       Ox "e49b69c1";
                       Ox "efbe4786";
                       Ox "0fc19dc6";
                       Ox "240ca1cc";
                       Ox "2de92c6f";
                       Ox "4a7484aa";
                       Ox "5cb0a9dc";
                       Ox "76f988da";
                       Ox "983e5152";
                       Ox "a831c66d";
                       Ox "b00327c8";
                       Ox "bf597fc7";
                       Ox "c6e00bf3";
                       Ox "d5a79147";
                       Ox "06ca6351";
                       Ox "14292967";
                       Ox "27b70a85";
                       Ox "2e1b2138";
                       Ox "4d2c6dfc";
                       Ox "53380d13";
                       Ox "650a7354";
                       Ox "766a0abb";
                       Ox "81c2c92e";
                       Ox "92722c85";
                       Ox "a2bfe8a1";
                       Ox "a81a664b";
                       Ox "c24b8b70";
                       Ox "c76c51a3";
                       Ox "d192e819";
                       Ox "d6990624";
                       Ox "f40e3585";
                       Ox "106aa070";
                       Ox "19a4c116";
                       Ox "1e376c08";
                       Ox "2748774c";
                       Ox "34b0bcb5";
                       Ox "391c0cb3";
                       Ox "4ed8aa4a";
                       Ox "5b9cca4f";
                       Ox "682e6ff3";
                       Ox "748f82ee";
                       Ox "78a5636f";
                       Ox "84c87814";
                       Ox "8cc70208";
                       Ox "90befffa";
                       Ox "a4506ceb";
                       Ox "bef9a3f7";
                       Ox "c67178f2"
                     ]%vector.


  (** The rotation and shift offsets for sha256 *)

  Definition R00 := 2.  Definition R01 := 13. Definition R02 := 22.
  Definition R10 := 6.  Definition R11 := 11. Definition R12 := 25.
  Definition r00 := 7.  Definition r01 := 18. Definition s0  := 3.
  Definition r10 := 17. Definition r11 := 19. Definition s1  := 10.

  Lemma increasing_R's : R00 <= R01 <= R02 /\ R10 <= R11 <= R12.
  Proof.
    repeat (compute; constructor).
  Qed.

  Definition increasing_r's : r00 <= r01 /\ r10 <= r11.
  Proof.
    repeat (compute; constructor).
  Qed.

End Config.
Module SHA256 := SHA2 Config.

Require Import Verse.Target.C.

Inductive name := verse_sha256_c_portable.

Require Verse.CryptoLib.sha2.

Module Allocation.

  Axiom blockPtr : cvar (ptrToArray sha2.BLOCK_SIZE uint32_t).
  Axiom nBlocks  : cvar uint64_t.
  Axiom hash     : cvar (ptrToArray sha2.HASH_SIZE uint32_t).
  Axiom w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : cvar uint32_t.
  Axiom a b c d e f g h : cvar uint32_t.
  Axiom t               : cvar uint32_t.

End Allocation.

Export Allocation.

Definition params    := (- hash -).
Definition locals    := (- w0 , w1 , w2 , w3 , w4 , w5 , w6 , w7 , w8 , w9 , w10 , w11 , w12 , w13,  w14 ,  w15 -).
Definition registers := (- a, b, c, d, e, f, g, h, t -).

Definition sha256iter
  := Compile.Iterator verse_sha256_c_portable
                      SHA256.Block
                      SHA256.parameters
                      SHA256.locals
                      SHA256.registers
                      blockPtr
                      nBlocks
                      params
                      locals
                      registers
                      SHA256.sha2.


Require Import Verse.Error.
Definition iterator : Compile.programLine := recover sha256iter.
Definition program := verseC [iterator].

Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI
  := ffi [ iterator verse_sha256_c_portable
                    SHA256.Block
                    SHA256.parameters
         ].


(*

Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.


Goal to_print program.
  print.
Abort.

*)
