Require Import Verse.
Require Import Verse.CryptoLib.blake2.
Require Import Verse.CryptoLib.blake2.c.portable.

Require Vector.
Import Vector.VectorNotations.

Module Config <: CONFIG.

  Definition Word   := Word64.
  Definition ROUNDS := 12.
  Definition IVVec  :=
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

Require Scope.

(*
Definition blake2bIter
  := Iterator verse_blake2b_c_portable_iter
              Blake2b.Block
              Blake2b.Compressor.
*)


Require Verse.Error.

(*
Definition  level0 := Scope.Cookup.specialise Blake2b.LastBlockCompressor.

Definition pvt : Scope.type _ _ :=
  let foo := Scope.unNestDelimited level0 in
  let pvs := fst foo  in
  Error.recover (Compile.targetTypes pvs).


Definition lvt : Scope.type _ _ := Error.recover (Compile.targetTypes lvs).

Definition paramsAndBody := Scope.unNestDelimited level0.
Definition pvs := fst paramsAndBody.
Definition level1 := snd paramsAndBody.
Definition lvs := Scope.infer level1.


       let (pA,n0) := Internals.calloc 0 pvt in
       let (lA,_) := Internals.calloc n0 lvt in
       Compile.function name pvs lvs
                        pvt     lvt
                        eq_refl eq_refl
                        pA      lA
     )
       (only parsing).
*)

Definition blake2bIter : CodeGen.Config.programLine + {Error.TranslationError}.
  Iterator verse_blake2b_c_portable_iter Blake2b.Block Blake2b.Compressor.
Defined.

Definition blake2bLast : CodeGen.Config.programLine + {Error.TranslationError}.
  Function verse_blake2b_c_portable_last
           Blake2b.LastBlockCompressor.
Defined.

Require Import Verse.Error.
Definition iterator   : Compile.programLine := recover (blake2bIter).
Definition lastchunk  : Compile.programLine := recover (blake2bLast).
Definition program := verseC [iterator; lastchunk].

Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name}(name : Name)
  := mkProgram name [ iterator verse_blake2b_c_portable_iter
                                Blake2b.Block
                                Blake2b.Compressor;
                      function verse_blake2b_c_portable_last
                                Blake2b.LastBlockCompressor
                    ].
Arguments raazFFI [Name].

(*

Require Import Verse.Print.
Require Import Verse.Target.C.Pretty.
Goal to_print program.
  print.
Abort.

*)
