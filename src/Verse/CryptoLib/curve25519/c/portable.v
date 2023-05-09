Require Import Verse.

(** * Curve 25519 and its parameters *)



Definition Word      := Word64.
Definition Element   := (Array 4 littleE Word).
Definition Scalar    := (Array 4 littleE Word).

Module Internal.

  Section Curve25519.
    Variable progvar : VariableT.

    (** ** Clamping the scalar [n].

        The elliptic curve secret consists of computing [n Q] for the
        base point [Q]. To ensure that the [nQ] falls into the
        appropriate prime order subgroup of Curve25519 group we need
        to clamp n appropriately.

     *)


    Definition clamp (T : progvar of type Word) (scalA : progvar of type Scalar) : code progvar.
      verse [code|
          T := scalA[ 0 ];
          T &= `Ox "ff:ff:ff:ff ff:ff:ff:f8"`;
          scalA[ 0 ] <- T;

          T := scalA[ 3 ];
          T &= `Ox "7f:ff:ff:ff ff:ff:ff:ff"`;
          T |= `Ox "40:00:00:00 00:00:00:00"`;
          scalA[ 3 ] <- T
        |].
    Defined.

    Definition clampIter (T : progvar of type Word) : iterator progvar Scalar
      := {| setup    := [];
            process  := clamp T;
            finalise := []
         |}%list.

    Definition ClampIter := do clampIter end.
  End Curve25519.

End Internal.



Inductive name := verse_curve25519_c_portable_clamp.

Require Import Verse.Target.C.
Require Import Verse.Error.


Definition clamp  : CodeGen.Config.programLine + {Error.TranslationError}.
  Iterator verse_curve25519_c_portable_clamp
           Scalar
           Internal.ClampIter.
Defined.

Definition clampI       : Compile.programLine := recover clamp.

Definition program := verseC [ clampI ].


Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name} (name : Name)
  := mkProgram name [ iterator verse_curve25519_c_portable_clamp
                               Scalar
                               Internal.ClampIter
                    ].
