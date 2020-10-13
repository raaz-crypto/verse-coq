Require Import Verse.BitVector.
Require Import Verse.Machine.BitVector.
Require Import Verse.AbstractMachine.
Require Import Verse.Monoid.
Require Import Verse.ScopeStore.

Require Import Verse.

Set Implicit Arguments.

Section Code.

  Variable v : VariableT.

  Variable A B : v Word8.

  Definition test : AnnotatedCode v bvDenote.
    annotated_verse
      [
        A ::= B;
        ASSERT (VAL A = OLDVAL A);
        A ::= B;
        ASSERT (OLDVAL B = BVplus (VAL A) BVones);
        A ::= B
      ]%code.
  Defined.

End Code.

Definition toProve : Prop.
  getProp test.
Defined.

Definition proof : toProve.
  simplify.
Abort.
