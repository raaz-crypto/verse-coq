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

Require Import Verse.Arch.C.

Module Internal.
  Definition Word := uint64_t.
  Definition reg := cr uint64_t.
  Definition cRegIterator :=
    (- reg "w0" , reg "w1" , reg "w2" , reg "w3" ,
       reg "w4" , reg "w5" , reg "w6" , reg "w7" ,
       reg "w8" , reg "w9" , reg "w10", reg "w11",
       reg "w12", reg "w13", reg "w14", reg "w15",
       reg "v0" , reg "v4" , reg "v8" , reg "v12",
       reg "v1" , reg "v5" , reg "v9" , reg "v13",
       reg "v2" , reg "v6" , reg "v10", reg "v14",
       reg "v3" , reg "v7" , reg "v11", reg "v15",
       reg "C"  , reg "LMSB",
       reg "U"  , reg "L"
    -).

  Definition cRegLast :=
    (- reg "w0" , reg "w1" , reg "w2" , reg "w3" ,
       reg "w4" , reg "w5" , reg "w6" , reg "w7" ,
       reg "w8" , reg "w9" , reg "w10", reg "w11",
       reg "w12", reg "w13", reg "w14", reg "w15",
       reg "v0" , reg "v4" , reg "v8" , reg "v12",
       reg "v1" , reg "v5" , reg "v9" , reg "v13",
       reg "v2" , reg "v6" , reg "v10", reg "v14",
       reg "v3" , reg "v7" , reg "v11", reg "v15",
       reg "C"  , reg "LMSB"
    -).



  Definition prototypeIter (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.iteratorPrototype Blake2b.Block fname Blake2b.paramIterator.
  Defined.

  Definition implementationIter (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator Blake2b.Block fname Blake2b.paramIterator Blake2b.stack Blake2b.regIterator.
    assignRegisters cRegIterator.
    statements Blake2b.Iterator.
  Defined.

  Definition prototypeLast (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.functionPrototype fname Blake2b.paramLastBlock.
  Defined.

  Definition implementationLast (fname : string) : Doc + {Compile.CompileError}.
    Compile.function fname Blake2b.paramLastBlock Blake2b.stack Blake2b.regLastBlock.
    assignRegisters cRegLast.
    statements Blake2b.LastBlockCompress.
  Defined.

  Definition iterName (fname : string) := fname ++ "_iter".
  Definition lastName (fname : string) := fname ++ "_last".

  Definition implementation (fname : string) : Doc + {Compile.CompileError} :=
    iter <- implementationIter (iterName fname);
      lastBlock <- implementationLast (lastName fname);
      {- vcat [iter; lastBlock] -}.

  Definition prototypes fname :=
    iterProto <- prototypeIter (iterName fname);
      lastProto <- prototypeLast (lastName fname);
      {- [ iterProto ; lastProto ]%list -}.

End Internal.

(*

This is the function that prints the code on the standard output given a function name
for the c-code.

 *)

Require Import Verse.Extraction.Ocaml.
Require Import Verse.CryptoLib.Names.
Require Import Verse.CryptoLib.Names.

Definition implementation_name : Name := {| primitive := "blake2b";
                                            arch      := "c";
                                            features  := ["portable"]
                                         |}.

Definition cname     := cFunName implementation_name.
Definition cfilename := libVerseFilePath implementation_name.

Definition implementation : unit
  := writeProgram (C cfilename) (Internal.implementation cname).

Definition prototypes
  := recover (Internal.prototypes cname).

Require Import Verse.FFI.Raaz.

Definition raazFFI : unit :=
  let module := raazModule implementation_name in
  write_module module (List.map ccall prototypes).
