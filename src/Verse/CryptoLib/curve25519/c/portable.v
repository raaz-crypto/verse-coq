Require Import Verse.
Import VerseNotations.


Definition Limb      := existT _ _ Word64.
Definition Element   := existT _ _ (Array 4 littleE (projT2 Limb)).
Definition Scalar    := existT _ _ (Array 4 littleE (projT2 Limb)).

Module Internal.

  Section Curve25519.
    Variable progvar : VariableT.

    (** ** Clamping the scalar [n].

        The elliptic curve secret consists of computing [n Q] for the
        base point [Q]. To ensure that the [nQ] falls into the
        appropriate prime order subgroup of Curve25519 group we need
        to clamp n appropriately.

     *)


    Definition clamp (T : progvar Limb)(scalA : progvar Scalar) : code progvar.
      verse [code|
          T := scalA[ `0` ];
          T &= `Ox "ff:ff:ff:ff ff:ff:ff:f8"`;
          scalA[ `0` ] <- T;

          T := scalA[ `3` ];
          T &= `Ox "7f:ff:ff:ff ff:ff:ff:ff"`;
          T |= `Ox "40:00:00:00 00:00:00:00"`;
          scalA[ `3` ] <- T
        |].
    Defined.

    Definition clampIter (T : progvar Limb) : iterator progvar (projT2 Scalar)
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
           (projT2 Scalar)
           Internal.ClampIter.
Defined.

Definition clampI       : Compile.programLine := recover clamp.

Definition program := verseC [ clampI ].


Require Import Verse.FFI.Raaz.
Require Import Verse.FFI.Raaz.Target.C.

Definition raazFFI {Name} (name : Name)
  := mkProgram name [ iterator verse_curve25519_c_portable_clamp
                               (projT2 Scalar)
                               Internal.ClampIter
                    ].
