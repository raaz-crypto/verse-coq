Require Import Verse.
Require Vector.
Import VectorNotations.
Delimit Scope vector_scope with vector.
Require Import List.
Import ListNotations.
Require Import Verse.CryptoLib.sha2.
Require Import Verse.CryptoLib.sha2.c.portable.

Module Config <: CONFIG.
  Definition Word := Word32.
  Definition ROUNDS := 63.
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

End Config.



Module SIG <: SIGMA (Config).
  Section SIGS.
    Variable v  : VariableT.
    Variable t  : v direct Config.Word.
    Variable tp : v direct Config.Word.
    Variable x  : v direct Config.Word.

    (* sigb0(x) = RotateR(x,2) ^ RotateR(x,13) ^ RotateR(x,22) *)


    Definition SIGB0 : code v := [ t ::=  x >*> 9;
                                   t ::=^ x;    (* t = x +  x >>> 9 *)
                                   t ::=>*> 11; (* t = x >>> 11 + x >>> 20 *)
                                   t ::=^ x;    (* t = x + x>>>11 + x>>>20 *)
                                   t ::=>*> 2   (* t = x >>> 2 + x >>> 13 + x >>> 22 *)
                                 ].
    (* define sigb1(x) = RotateR(x,6) ^ RotateR(x,11) ^ RotateR(x,25) *)

    Definition SIGB1 : code v := [ t ::= x >*> 14;
                                   t ::=^ x;    (* t = x +  x >>> 14 *)
                                   t ::=>*> 5;  (* t = x >>> 5 + x >>> 19 *)
                                   t ::=^ x;    (* t = x + x>>>5 + x>>>19 *)
                                   t ::=>*> 6   (* t = x >>> 6 + x >>> 11 + x >>> 25 *)

                                 ].

    (* sigs0(x)     (RotateR(x,7) ^ RotateR(x,18) ^ ShiftR(x,3)  *)
    (* sigs1(x)     (RotateR(x,17) ^ RotateR(x,19) ^ ShiftR(x,10)  *)
    Definition SIGS0 : code v := [ tp ::=  x >> 3;
                                   t  ::=  x >*> 11;
                                   t  ::=^ x;        (* t = x ^ x >>> 11                *)
                                   t  ::=>*> 7;      (* t = x >>> 7 ^ x >>> 18          *)
                                   t  ::=^ tp        (* t = x >>> 7 ^ x >>> 18 ^ x >> 3 *)
                                 ].
    Definition SIGS1 : code v := [ tp ::=  x >> 10;
                                   t  ::=  x >*> 2;
                                   t  ::=^ x;        (* t = x ^ x >>> 2                *)
                                   t  ::=>*> 17;      (* t = x >>> 17 ^ x >>> 19       *)
                                   t  ::=^ tp        (* t = x >>> 17 ^ x >>> 19 ^ x >> 10 *)
                                 ].

    End SIGS.

End SIG.

Require Import Verse.Arch.C.
Module SHA256 := SHA2 Config SIG.
Import Config.

Module Internal.

  Definition regVars
    := (- cr Word "a",  cr Word "b",  cr Word "c",  cr Word "d",
          cr Word "e",  cr Word "f",  cr Word "g",  cr Word "h",
          cr Word "t",  cr Word "tp",  cr Word "temp"
                                       -).

  Definition sha256 (fname : string) : Doc + {Compile.CompileError}.
    Compile.iterator SHA256.Block fname SHA256.parameters SHA256.locals SHA256.registers.
    assignRegisters regVars.
    statements SHA256.sha2.
  Defined.
End Internal.

(*

This is the function that prints the code on the standard output given a function name
for the c-code.

*)

Require Import Verse.Extraction.Ocaml.
Definition implementation (fp cfunName : string) : unit := writeProgram (C fp) (Internal.sha256 cfunName).
