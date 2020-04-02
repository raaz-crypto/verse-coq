Inductive Name := ModuleName.
Notation "'Raaz.Verse.PRIM.C.Portable'" := ModuleName (only printing).


Require Import Verse.CryptoLib.translit(PRIM,A-Z,a-z).c.portable.
Require Import Verse.FFI.Raaz.
Require Import Verse.Print.

Goal to_print (raazFFI ModuleName).
  print.
Abort.
