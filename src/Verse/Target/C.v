Require Import Verse.Target.
Require Import Verse.Target.C.CodeGen.

Module Compile := Target.CodeGen (C.CodeGen.Config).

Require Export Verse.Target.C.Ast.
Require Export Verse.Target.C.Pretty.
