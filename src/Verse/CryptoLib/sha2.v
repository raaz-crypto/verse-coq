Require Import Verse.
Require Vector.
Import VectorNotations.
Delimit Scope vector_scope with vector.

(**

This module contains the common code fragment that is required by two
hashes SHA256 and SHA512.

 *)

Definition HASH_SIZE : nat := 8.
Definition BLOCK_SIZE : nat := 16.

Module Type CONFIG.

  (** The word type for the hash *)
  Parameter Word : type direct.

  (** The number of rounds that is involved in hashing *)
  Parameters ROUNDS : nat.
  (** The round constants for the hash *)
  Parameter KVec : Vector.t (constant Word) ROUNDS.

End CONFIG.

Module SHA256Config <: CONFIG.
  Definition Word := Word32.
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
                     ].

End SHA256Config.

Module SHA512Config <: CONFIG.
  Definition Word   := Word64.
  Definition ROUNDS := 80.
  Definition KVec   := [ Ox "428a2f98d728ae22";
                         Ox "7137449123ef65cd";
                         Ox "b5c0fbcfec4d3b2f";
                         Ox "e9b5dba58189dbbc";
                         Ox "3956c25bf348b538";
                         Ox "59f111f1b605d019";
                         Ox "923f82a4af194f9b";
                         Ox "ab1c5ed5da6d8118";
                         Ox "d807aa98a3030242";
                         Ox "12835b0145706fbe";
                         Ox "243185be4ee4b28c";
                         Ox "550c7dc3d5ffb4e2";
                         Ox "72be5d74f27b896f";
                         Ox "80deb1fe3b1696b1";
                         Ox "9bdc06a725c71235";
                         Ox "c19bf174cf692694";
                         Ox "e49b69c19ef14ad2";
                         Ox "efbe4786384f25e3";
                         Ox "0fc19dc68b8cd5b5";
                         Ox "240ca1cc77ac9c65";
                         Ox "2de92c6f592b0275";
                         Ox "4a7484aa6ea6e483";
                         Ox "5cb0a9dcbd41fbd4";
                         Ox "76f988da831153b5";
                         Ox "983e5152ee66dfab";
                         Ox "a831c66d2db43210";
                         Ox "b00327c898fb213f";
                         Ox "bf597fc7beef0ee4";
                         Ox "c6e00bf33da88fc2";
                         Ox "d5a79147930aa725";
                         Ox "06ca6351e003826f";
                         Ox "142929670a0e6e70";
                         Ox "27b70a8546d22ffc";
                         Ox "2e1b21385c26c926";
                         Ox "4d2c6dfc5ac42aed";
                         Ox "53380d139d95b3df";
                         Ox "650a73548baf63de";
                         Ox "766a0abb3c77b2a8";
                         Ox "81c2c92e47edaee6";
                         Ox "92722c851482353b";
                         Ox "a2bfe8a14cf10364";
                         Ox "a81a664bbc423001";
                         Ox "c24b8b70d0f89791";
                         Ox "c76c51a30654be30";
                         Ox "d192e819d6ef5218";
                         Ox "d69906245565a910";
                         Ox "f40e35855771202a";
                         Ox "106aa07032bbd1b8";
                         Ox "19a4c116b8d2d0c8";
                         Ox "1e376c085141ab53";
                         Ox "2748774cdf8eeb99";
                         Ox "34b0bcb5e19b48a8";
                         Ox "391c0cb3c5c95a63";
                         Ox "4ed8aa4ae3418acb";
                         Ox "5b9cca4f7763e373";
                         Ox "682e6ff3d6b2b8a3";
                         Ox "748f82ee5defb2fc";
                         Ox "78a5636f43172f60";
                         Ox "84c87814a1f0ab72";
                         Ox "8cc702081a6439ec";
                         Ox "90befffa23631e28";
                         Ox "a4506cebde82bde9";
                         Ox "bef9a3f7b2c67915";
                         Ox "c67178f2e372532b";
                         Ox "ca273eceea26619c";
                         Ox "d186b8c721c0c207";
                         Ox "eada7dd6cde0eb1e";
                         Ox "f57d4f7fee6ed178";
                         Ox "06f067aa72176fba";
                         Ox "0a637dc5a2c898a6";
                         Ox "113f9804bef90dae";
                         Ox "1b710b35131c471b";
                         Ox "28db77f523047d84";
                         Ox "32caab7b40c72493";
                         Ox "3c9ebe0a15c9bebc";
                         Ox "431d67c49c100d4c";
                         Ox "4cc5d4becb3e42b6";
                         Ox "597f299cfc657e2a";
                         Ox "5fcb6fab3ad6faec";
                         Ox "6c44198c4a475817"
                       ].
End SHA512Config.
