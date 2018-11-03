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

Require Import Verse.Arch.C.

Module Internal.
  Definition Word := uint32_t.
  Definition reg := cr uint32_t.
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
    Compile.iteratorPrototype Blake2s.Block fname Blake2s.paramIterator.
  Defined.

  Definition implementationIter (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator Blake2s.Block fname Blake2s.paramIterator Blake2s.stack Blake2s.regIterator.
    assignRegisters cRegIterator.
    statements Blake2s.Iterator.
  Defined.

  Definition prototypeLast (fname : string) : Prototype CType + {Compile.CompileError}.
    Compile.functionPrototype fname Blake2s.paramLastBlock.
  Defined.

  Definition implementationLast (fname : string) : Doc + {Compile.CompileError}.
    Compile.function fname Blake2s.paramLastBlock Blake2s.stack Blake2s.regLastBlock.
    assignRegisters cRegLast.
    statements Blake2s.LastBlockCompress.
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

Definition implementation_name : Name := {| primitive := "blake2s";
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
